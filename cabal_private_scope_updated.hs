{-# LANGUAGE OverloadedStrings #-}

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Control.Monad
import Data.Maybe
import Debug.Trace
import Data.Graph
import Data.List (sortBy, groupBy, intercalate)
import Data.Ord (comparing)
import Data.Containers.ListUtils (nubOrd)
import Control.Monad.State
import Control.Monad.RWS
import Text.Printf (printf)

type PackageName = String
type Version     = Int

data VersionRange = VR [Version]
  deriving (Eq, Show)

data Dependency = Dependency { depPackageName :: PackageName, depVersionRange :: VersionRange }
  deriving (Eq, Show)

data ScopeType = Public | Private PackageName Version String
  deriving (Eq, Ord, Show)

data SourceScope = PublicSrc | PrivateSrc String deriving (Eq, Ord)

sourceScopeToScopeType :: PackageName -> Version -> ScopeType -> SourceScope -> ScopeType
sourceScopeToScopeType _ _ parent_scope PublicSrc = parent_scope
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


data ListT m a = ConsT a (m (ListT m a)) | NilT

bindList :: (s -> [(a, s)]) -> (s -> [(a -> b, s)]) -> s -> [(b, s)]
bindList f g s = [ (b a, s'') | (a, s') <- f s, (b, s'') <- g s' ]

data RevDepMap = RevDepMap
  { revDeps :: Map QPN [QPN]
    -- ^ The reverse dependencies
  , privScopes :: Map String {- a private qualifier -} (Set.Set QPN) {- caches the packages in this private scope -}
    -- ^ Information related to reverse dependency mapped additionally cached here.
  }

-- Debug printing helpers
debugIndent :: Int -> String
debugIndent depth = replicate (depth * 2) ' '

-- Helper function for tracing guard failures
traceGuard :: Int -> QPN -> String -> Bool -> RWST () Result Assignment [] ()
traceGuard depth qpn reason condition = do
  if condition
    then return ()
    else do
      traceM $ debugIndent depth ++ "🚫 GUARD FAILED: " ++ showQPN qpn ++ " - " ++ reason
      mzero

showQPN :: QPN -> String
showQPN (QPN scope pkgName) = pkgName ++ "[" ++ showScope scope ++ "]"

showScope :: ScopeType -> String
showScope Public = "Public"
showScope (Private pkgName version name) =
  printf "Private(%s-%d:%s)" pkgName version name

showVersionRange :: VersionRange -> String
showVersionRange (VR versions) = "{" ++ intercalate "," (map show versions) ++ "}"

showPath :: [QPN] -> String
showPath path = intercalate " -> " (map showQPN (reverse path))

showScopesMap :: Map ScopeType (Set.Set PackageName) -> String
showScopesMap scopes
  | Map.null scopes = "{}"
  | otherwise = "{" ++ intercalate ", "
    [ showScope scope ++ "->{" ++ intercalate "," (Set.toList pkgs) ++ "}"
    | (scope, pkgs) <- Map.toList scopes
    ] ++ "}"

showPublicMap :: Map PackageName ScopeType -> String
showPublicMap public_map
  | Map.null public_map = "{}"
  | otherwise = "{" ++ intercalate ", "
    [ pkgName ++ "->" ++ showScope scope
    | (pkgName, scope) <- Map.toList public_map
    ] ++ "}"

-- Enhanced debug printing for solve function
debugSolve :: Int -> QPN -> VersionRange -> Map ScopeType (Set.Set PackageName) -> Map PackageName ScopeType -> [QPN] -> String
debugSolve depth qpn vr scopes public_map path =
  debugIndent depth ++ "🔍 SOLVE: " ++ showQPN qpn ++ " " ++ showVersionRange vr ++ "\n" ++
  debugIndent depth ++ "   Path: " ++ showPath path ++ "\n" ++
  debugIndent depth ++ "   Scopes: " ++ showScopesMap scopes ++ "\n" ++
  debugIndent depth ++ "   Public Map: " ++ showPublicMap public_map

debugSolveResult :: Int -> QPN -> Version -> String
debugSolveResult depth qpn version =
  debugIndent depth ++ "✅ RESULT: " ++ showQPN qpn ++ " -> " ++ show version

debugSolveBacktrack :: Int -> QPN -> VersionRange -> String
debugSolveBacktrack depth qpn vr =
  debugIndent depth ++ "❌ BACKTRACK: " ++ showQPN qpn ++ " " ++ showVersionRange vr ++ " (no valid version)"

debugSolveCached :: Int -> QPN -> Version -> String
debugSolveCached depth qpn version =
  debugIndent depth ++ "💾 CACHED: " ++ showQPN qpn ++ " -> " ++ show version

debugSolveVersion :: Int -> QPN -> Version -> String
debugSolveVersion depth qpn version =
  debugIndent depth ++ "🎯 TRYING: " ++ showQPN qpn ++ " -> " ++ show version

debugSolveDeps :: Int -> [(SourceScope, [Dependency])] -> String
debugSolveDeps depth deps =
  debugIndent depth ++ "📦 DEPS: " ++
  intercalate ", "
    [ showSourceScope scope ++ "->[" ++
      intercalate "," [ depPackageName dep ++ showVersionRange (depVersionRange dep) | dep <- deps' ] ++ "]"
    | (scope, deps') <- deps
    ]

showSourceScope :: SourceScope -> String
showSourceScope PublicSrc = "Public"
showSourceScope (PrivateSrc name) = "Private(" ++ name ++ ")"

-- Main solving function
solve :: PackageDB
      -> Map.Map ScopeType (Set.Set PackageName) -- ^ Definition of scopes
      -> Map.Map PackageName ScopeType           -- ^ Which scope each package should be solved in.
      -> [QPN]
      -> (QPN, VersionRange)
      -> RWST () Result Assignment [] (QPN, Version)
solve db scopes public_map path ((qpn@(QPN parentScope name), vr)) = do
  let depth = length path
  traceM $ debugSolve depth qpn vr scopes public_map path
  assignment <- get
  case Map.lookup qpn assignment of
    Just v | satisfies v vr -> do
                traceGuard depth qpn ("closure property check failed:" ++ showPath (qpn : path)) $ checkClosedTop parentScope path
                traceM $ debugSolveCached depth qpn v
                pure (qpn, v)
           | otherwise      -> do
                traceM $ debugSolveBacktrack depth qpn vr
                mzero
    Nothing -> do
      pkg <- lift $ maybeToList (Map.lookup name db)
      v   <- lift $ availableVers pkg
      traceGuard depth qpn ("version " ++ show v ++ " does not satisfy range " ++ showVersionRange vr) $ satisfies v vr
      traceGuard depth qpn ("closure property check failed:" ++ showPath (qpn : path)) $ checkClosedTop parentScope path
      traceM $ debugSolveVersion depth qpn v

      -- Record our choice of assignment.
      modify $ Map.insert qpn v

      -- Add the current package to its scope in the scopes map
      let new_scopes :: Map ScopeType (Set.Set PackageName)
          new_scopes = Map.fromList [(Private name v sc, Set.fromList (map depPackageName deps)) | (PrivateSrc sc, deps) <- dependencies pkg v]

          scopes' = scopes `Map.union` new_scopes

          transitive_scopes Public = public_map
          transitive_scopes p =
            case Map.lookup p scopes of
              Just pkgs ->
                public_map
                `Map.union`
                Map.fromList [(pkgs, p) | pkgs <- Set.toList pkgs]
              Nothing -> error "not found" -- Impossible, since the scope must be defined before it is used.

          get_dep_scope :: PackageName -> ScopeType
          get_dep_scope pn = case Map.lookup pn (transitive_scopes parentScope) of
            Just sc -> sc
            Nothing -> Public

      -- Get dynamic scope and dependencies
      let mkQDeps depScope deps = [ (QPN (sourceScopeToScopeType name v (get_dep_scope dn) depScope) dn, vr') | Dependency dn vr' <- deps ]

      let path' = qpn : path

      let deps = dependencies pkg v
      traceM $ debugSolveDeps depth deps

      deps <- mapM ((\(sc, ds) -> (sc,) <$> mapM (solve db scopes' (transitive_scopes parentScope) path') (mkQDeps sc ds))) deps
      -- Storing result
      tell $ Map.singleton qpn (v, deps)
      traceM $ debugSolveResult depth qpn v
      pure (qpn, v)
    where


checkClosedTop Public _ = True
checkClosedTop s@(Private {}) p = checkClosed s p

-- Check closed checks the closure property of private dependencies.Foreign
-- When a node is chosen to be in a private scope, then we check the closure property of the specific path
-- which led to that node.

-- checkClosed takes the scope of the added node and a path in reverse order (the first element is the parent of the node we just added).
-- For the closure property to hold, it must have the structure of
--   * nodes also in the private scope, followed by nodes not in the private scope.
checkClosed :: ScopeType -> [QPN] -> Bool
checkClosed scope [] = True
checkClosed scope ((QPN scope' _):rest) =
  if scope == scope' then checkClosed scope rest else checkNotScope scope rest

checkNotScope :: ScopeType -> [QPN] -> Bool
checkNotScope scope [] = True
checkNotScope scope ((QPN scope' _) : rest) =  scope /= scope' && checkNotScope scope rest

-- Unit tests for checkClosed function
test_checkClosed :: IO ()
test_checkClosed = do
  putStrLn "Running checkClosed unit tests..."

  -- Test 1: Empty path should be closed
  let test1 = checkClosed (Private "S" 1 "test") []
  putStrLn $ "Test 1 (empty path): " ++ show test1 ++ " (expected: True)"

  -- Test 2: Path with only public packages should be closed
  let test2 = checkClosed (Private "S" 1 "test")
                [QPN Public "A", QPN Public "B", QPN Public "C"]
  putStrLn $ "Test 2 (only public packages): " ++ show test2 ++ " (expected: True)"

  -- Test 3: Path with adjacent private packages should be closed
  let test3 = checkClosed (Private "S" 1 "test")
                [QPN (Private "S" 1 "test") "B", QPN (Private "S" 1 "test") "C", QPN Public "D"]
  putStrLn $ "Test 3 (adjacent private packages): " ++ show test3 ++ " (expected: True)"

  -- Test 4: Path with non-adjacent private packages should NOT be closed
  let test4 = checkClosed (Private "S" 1 "test")
                [QPN (Private "S" 1 "test") "A", QPN Public "B", QPN (Private "S" 1 "test") "C"]
  putStrLn $ "Test 4 (non-adjacent private packages): " ++ show test4 ++ " (expected: False)"

  -- Test 5: Path with mixed scopes but adjacent private packages should be closed
  let test5 = checkClosed (Private "S" 1 "test")
                [QPN (Private "S" 1 "test") "B", QPN (Private "S" 1 "test") "C", QPN Public "D"]
  putStrLn $ "Test 5 (mixed scopes, adjacent private): " ++ show test5 ++ " (expected: True)"

  -- Test 6: Path with private packages from different scopes should be closed
  let test6 = checkClosed (Private "S" 1 "test")
                [QPN (Private "S" 1 "test") "A", QPN (Private "T" 1 "other") "B", QPN (Private "T" 1 "test") "C"]
  putStrLn $ "Test 6 (different private scopes): " ++ show test6 ++ " (expected: True)"

  putStrLn "checkClosed unit tests completed.\n"

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

-- This needs to force B into private scope
simpleDB :: PackageDB
simpleDB = Map.fromList
  [ ("A", Package "A" [1] $ \_ -> [(PublicSrc, [Dependency "B" (VR [1])])])
  , ("B", Package "B" [1] $ \_ -> [(PublicSrc, [Dependency "C" (VR [1])])])
  , ("C", Package "C" [1] $ \_ -> [])
  , ("S", Package "S" [1] $ \_ -> [(PrivateSrc "S", [Dependency "C" (VR [1]), Dependency "A" (VR [1])])])
  ]

simpleDB2 :: PackageDB
simpleDB2 = Map.fromList
  [ ("A", Package "A" [1] $ \_ -> [(PublicSrc, [Dependency "B" (VR [1])])])
  , ("B", Package "B" [1] $ \_ -> [(PublicSrc, [Dependency "C" (VR [1])])])
  , ("C", Package "C" [1] $ \_ -> [])
  , ("S", Package "S" [1] $ \_ -> [(PrivateSrc "S", [Dependency "C" (VR [1]), Dependency "B" (VR [1]), Dependency "A" (VR [1])])])
  ]

simplestDB :: PackageDB
simplestDB = Map.fromList
  [ ("B", Package "B" [1] $ \_ -> [(PublicSrc, [Dependency "C" (VR [1, 2])])])
  , ("C", Package "C" [1, 2, 3] $ \_ -> [])
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
  -- Run unit tests for checkClosed function
  -- test_checkClosed

  let initialGoals = [ (QPN Public "S", VR [1]) ]


{-
  do_solve [(QPN Public "B", VR [1])] simplestDB


  do_solve initialGoals exampleDB
  -}

  do_solve initialGoals simpleDB

do_solve :: [(QPN, VersionRange)] -> PackageDB -> IO ()
do_solve initialGoals db = do
  let solutions = nubOrd $ runRWST (mapM (solve db Map.empty Map.empty []) initialGoals) () Map.empty
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
    showQPNs = unwords . map (\(QPN _ pkgName, version) -> pkgName ++ "-" ++ show version)



