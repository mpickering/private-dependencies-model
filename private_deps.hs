{-# LANGUAGE OverloadedStrings #-}

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Control.Monad
import Data.Maybe
import Debug.Trace
import Data.Graph
import Data.List (sortBy, groupBy)
import Data.Ord (comparing)
import Data.Containers.ListUtils (nubOrd)
import Control.Monad.State
import Control.Monad.RWS

type PackageName = String
type Version     = Int

data VersionRange = VR [Version]
  deriving (Eq, Show)

data Dependency = Dependency PackageName VersionRange
  deriving (Eq, Show)

data ScopeType = Public | Private PackageName Version String
  deriving (Eq, Ord, Show)

data SourceScope = PublicSrc | PrivateSrc String deriving (Eq, Ord)

sourceScopeToScopeType :: PackageName -> Version -> ScopeType -> SourceScope -> ScopeType
sourceScopeToScopeType _ _ parent PublicSrc = parent
sourceScopeToScopeType pn v _ (PrivateSrc name) = Private pn v name


data QPN = QPN { qpnScope :: ScopeType, qpnPackage :: PackageName }
  deriving (Eq, Ord, Show)

-- Now dependencies can introduce a new scope dynamically
data Package = Package
  { pkgName       :: PackageName
  , availableVers :: [Version]
  , dependencies  :: Version -> [(SourceScope, [Dependency])]
  }

type PackageDB = Map PackageName Package
type Assignment = Map QPN Version


type Result = Map.Map QPN (Version, [(SourceScope, [(QPN, Version)])])

-- Main solving function
solve :: PackageDB -> Set.Set ScopeType
      -> (QPN, VersionRange) -> RWST () Result Assignment [] (QPN, Version)
solve db scopes ((qpn@(QPN parentScope name), vr)) = do
  assignment <- get
  case Map.lookup qpn assignment of
    Just v | satisfies v vr -> pure (qpn, v)
           | otherwise      -> mzero
    Nothing -> do
      pkg <- lift $ maybeToList (Map.lookup name db)
      v   <- lift $ availableVers pkg
      guard (satisfies v vr)
      -- Record our choice of assignment.
      modify $ Map.insert qpn v

      -- A set of all previously seen scopes
      let scopes' = Set.insert parentScope scopes
      scope <- lift $ Set.toList scopes'


      -- Get dynamic scope and dependencies
      let mkQDeps depScope deps = [ (QPN (sourceScopeToScopeType name v scope depScope) dn, vr') | Dependency dn vr' <- deps ]

      traceShowM (scopes, qpn, vr)
      deps <- mapM ((\(sc, ds) -> (sc,) <$> mapM (solve db scopes') (mkQDeps sc ds))) (dependencies pkg v)
      tell $ Map.singleton qpn (v, deps)
      pure (qpn, v)

satisfies :: Version -> VersionRange -> Bool
satisfies v (VR vs) = v `elem` vs

-- Example: C -> B -> A -> D, with no new nested private scopes
exampleDB :: PackageDB
exampleDB = Map.fromList
  [ ("C", Package "C" [1] $ \_ -> [(PublicSrc, [Dependency "B" (VR [1])])])
  , ("B", Package "B" [1] $ \_ -> [(PublicSrc, [Dependency "A" (VR [1])])])
  , ("A", Package "A" [1] $ \_ -> [(PublicSrc, [Dependency "D" (VR [1])])])
  , ("D", Package "D" [1] $ \_ -> [(PublicSrc, [])])
  , ("S", Package "S" [1] $ \_ -> [(PrivateSrc "S", [Dependency "C" (VR [1]),Dependency "A" (VR [1])])])
  ]

simpleDB :: PackageDB
simpleDB = Map.fromList
  [ ("A", Package "A" [1] $ \_ -> [(PublicSrc, [Dependency "B" (VR [1])])])
  , ("B", Package "B" [1] $ \_ -> [(PublicSrc, [Dependency "C" (VR [1])])])
  , ("C", Package "C" [1] $ \_ -> [])
  , ("S", Package "S" [1] $ \_ -> [(PrivateSrc "S", [Dependency "A" (VR [1])])])
  ]

type PNV = (PackageName, Version)

{-
-- Create a graph from PackageDB using containers Data.Graph
-- where vertices are (PackageName, Version) pairs
createPackageGraph :: PackageDB -> (Graph, Vertex -> (PNV, PNV, [PNV]), PNV -> Maybe Vertex)
createPackageGraph db = graphFromEdges allVertices
  where
    allVertices :: [(PNV, PNV, [PNV])]
    allVertices = [((pkgName, version), (pkgName, version), deps)
                   | (pkgName, pkg) <- Map.toList db
                   , version <- availableVers pkg
                   , (PublicSrc, deps) <- [dependencies pkg version]

                   ] -}


-- Helper function to get (PackageName, Version) from vertex index
vertexToPackageVersion :: PackageDB -> Vertex -> Maybe (PackageName, Version)
vertexToPackageVersion db vertex =
  let allVertices = [(pkgName, version)
                     | (pkgName, pkg) <- Map.toList db
                     , version <- availableVers pkg]
      indexToVertex = Map.fromList $ zip [0..] allVertices
  in Map.lookup vertex indexToVertex

-- Pretty print a solution
prettyPrintSolution :: Result -> IO ()
prettyPrintSolution result = do
  putStrLn "=== Solution ==="

  -- Group QPNs by scope type
  let assignments = Map.toList result
      groupedByScope = groupBy (\a b -> getScope (fst a) == getScope (fst b))
                               (sortBy (comparing (getScope . fst)) assignments)

  mapM_ printScopeGroup groupedByScope
  putStrLn "================"
  where
    getScope (QPN scope _) = scope

    printScopeGroup [] = return ()
    printScopeGroup ((qpn@(QPN scope pkgName), (version, scopeDeps)):rest) = do
      putStrLn $ "Scope: " ++ showScope scope
      putStrLn $ "  " ++ pkgName ++ " -> " ++ show version
      putStrLn $ "  " ++ pkgName ++ " dependencies:"
      mapM_ (\(sourceScope, deps) -> do
        putStrLn $ "    From " ++ showSourceScope sourceScope ++ ":"
        mapM_ (\(QPN depScope depName, depVersion) ->
          putStrLn $ "      -> " ++ depName ++ " -> " ++ show depVersion ++ " (in " ++ showScope depScope ++ ")") deps
        ) scopeDeps
      putStrLn ""
      -- Continue with remaining packages in different scopes
      printScopeGroup rest

    showScope Public = "Public"
    showScope (Private pkgName version name) =
      "Private(" ++ pkgName ++ "-" ++ show version ++ ":" ++ name ++ ")"

    showSourceScope PublicSrc = "Public"
    showSourceScope (PrivateSrc name) = "Private(" ++ name ++ ")"

-- Pretty print multiple solutions
prettyPrintSolutions :: [Result] -> IO ()
prettyPrintSolutions [] = putStrLn "No solutions found."
prettyPrintSolutions solutions = do
  putStrLn $ "Found " ++ show (length solutions) ++ " solution(s):"
  putStrLn ""
  zipWithM_ (\i sol -> do
    putStrLn $ "Solution " ++ show i ++ ":"
    prettyPrintSolution sol
    putStrLn "") [1..] solutions

data ClosureCheck = Closed | NotClosed [(QPN, Version)] [(QPN, Version)] deriving (Eq, Ord)

-- Check closure property for a Result with detailed diagnostics
checkClosurePropertyDetailed :: Assignment -> Result -> [(ScopeType, ClosureCheck)]
checkClosurePropertyDetailed assignment result = [ (scope, do_scope scope) | scope <- Set.toList privateScopes ]
  where
    -- Get all private scopes from the result
    privateScopes = Set.fromList [scope | (QPN scope _, _) <- Map.toList result, Private pn v s <- [scope]]

    nodes = Map.keys assignment

    do_scope scope = if graph_roots == scope_vertices then Closed else NotClosed graph_roots scope_vertices
      where
        -- A graph
        graph_roots = [(pkgName, version)
                        | (pkgName, (version, _)) <- Map.toList result
                        , qpnScope pkgName == scope
                       ]

        graph_edges done acc [] = acc
        graph_edges done acc (pkgName:rest)
          | pkgName `Set.member` done = graph_edges done acc rest
          | otherwise =
            let Just (_,deps) = Map.lookup (fst pkgName) result
                public_deps = [ d | (PublicSrc, ds) <- deps, d <- ds ]

            in graph_edges (Set.insert pkgName done) (((pkgName, pkgName, public_deps)) : acc) (rest ++ public_deps)

        (g1, from_vertex, to_vertex) = graphFromEdges $ graph_edges Set.empty [] graph_roots
        g2 = dfs  (transposeG g1) (map (fromJust . to_vertex) graph_roots)

        scope_vertices = [a | (a,_,_) <- map (from_vertex) $ preorderF g2]


preorder' :: Tree a -> [a] -> [a]
preorder' (Node a ts) = (a :) . preorderF' ts

preorderF' :: [Tree a] -> [a] -> [a]
preorderF' ts = foldr (.) id $ map preorder' ts

preorderF :: [Tree a] -> [a]
preorderF ts = preorderF' ts []



checkClosureProperty :: Assignment -> Result -> Bool
checkClosureProperty assignment result =
  all (\(_, check) -> check == Closed) (checkClosurePropertyDetailed assignment result)

main :: IO ()
main = do
  let initialGoals = [ (QPN Public "S", VR [1]) ]

  do_solve initialGoals exampleDB

  do_solve initialGoals simpleDB

do_solve :: [(QPN, VersionRange)] -> PackageDB -> IO ()
do_solve initialGoals db = do
  let solutions = nubOrd $ runRWST (mapM (solve db Set.empty) initialGoals) () Map.empty
      results = map (\(_, _, result) -> result) solutions
      assignments = map (\(assignment, _, _) -> assignment) solutions

  prettyPrintSolutions results

  -- Print closure check results
  putStrLn "\n=== Closure Property Check ==="
  zipWithM_ (\i (_, assignment, result) -> do
    putStrLn $ "Solution " ++ show i ++ " closure check:"
    let closureChecks = checkClosurePropertyDetailed assignment result
    mapM_ (\(scope, check) -> do
      putStrLn $ "  Scope " ++ showScope scope ++ ": "
      case check of
        NotClosed roots vertices -> do
          putStrLn $ "    Graph roots: " ++ showQPNs roots
          putStrLn $ "    Scope vertices: " ++ showQPNs vertices
          let extraInClosure = filter (`notElem` roots) vertices
          when (not $ null extraInClosure) $
            putStrLn $ "    Extra in closure: " ++ showQPNs extraInClosure
        _ -> return ()
      ) closureChecks
    putStrLn $ "  All scopes closed: " ++ show (checkClosureProperty assignment result)
    putStrLn ""
    ) [1..] solutions
  where
    showScope Public = "Public"
    showScope (Private pkgName version name) =
      "Private(" ++ pkgName ++ "-" ++ show version ++ ":" ++ name ++ ")"

    showQPNs = unwords . map (\(QPN _ pkgName, version) -> pkgName ++ "-" ++ show version)



