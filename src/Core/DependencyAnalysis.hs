{-# LANGUAGE LambdaCase #-}

module Core.DependencyAnalysis where

{- Dependency analysis

   Core-to-Core transformation with the goal of simplifying letrec
   expressions by detecting minimal sets of mutually recursive
   definitions and eliminating redundant uses of the construct
   in non-recursive bindings by transforming them into normal let
   expressions.

   Given a letrec expression

     letrec x_1 = M_1
            x_2 = M_2
            ...
            x_n = M_n
     in E

   We create structures (a, [a]), where (x_i, xs) is such that
   xs is a sublist of the variables bound by the construct such that
   every variable in the list occurs free in M_i.

   From these structures we create the dependency graph:
   the dependency graph has a directed edge (x_i, x_j) iff x_j occurs free in
   M_i.

   From the dependency graph, we compute strongly connected components which
   represent maximal sets of mutually recursive definitions in the letrec.
   SCCs of a single vertex that does not point to itself represent non-recursive
   definitions. These will be transformed to (non-recursive) let expressions.
   Other SCCs will represent letrecs where the bound variables are given by the
   vertices of the component.

   The SCCs are computed in (reversed) topological sort: if v1 in C1 points
   to v2 in C2, then C2 occurs before C1 in the sort. In this setting,
   the let(rec) corresponding to C2 will contain the definition of that of C1,
   ensuring that all definitions on which a letrec depends are already in scope.

-}

import qualified Data.List.NonEmpty as NE (toList, map, NonEmpty(..))
import Data.Tuple(swap)
import Data.Set(Set, intersection, fromList, toList)
import Control.Arrow(second)
import Data.Graph(flattenSCC, Graph, Vertex, SCC, graphFromEdges)
import Data.Graph.SCC(sccList)
import Core.Syntax
import Utils
import AST
import RecursionSchemes

--------------------------------------------------------------------------------
-- Main function

depAnalysisTrans :: Ord a => CoreExpr a -> CoreExpr a
depAnalysisTrans = para $ \case
  (ELetF Recursive b e) -> transformLetRec (fmap (fmap fst) b) (snd e)
  e -> FixB . fmap snd $ e

--------------------------------------------------------------------------------
-- Dependency analysis and letrec transformation

data Classification a = ClNonRecursive (CoreBinder a)
                      | ClRecursive [CoreBinder a]

type DAGraphMap a = Vertex -> (CoreExpr a, a, [a])

transformLetRec :: Ord a
                => NE.NonEmpty (CoreBinder a)
                -> CoreExpr a
                -> CoreExpr a
transformLetRec b e = foldr instClassif e classified
  where
    b' = NE.toList . fmap pairify $ b
    (graph, dagMap) = dependencyGraph . computePreliminaryStructure $ b'
    sccs = sccList graph
    classified = classifySCCs dagMap sccs
    pairify (BinderB x y) = (x,y)

instClassif :: Classification a -> CoreExpr a -> CoreExpr a
instClassif (ClNonRecursive b) e = ELet NonRecursive (b NE.:| []) e
instClassif (ClRecursive bs) e = ELet Recursive (head bs NE.:| tail bs) e

computePreliminaryStructure :: Ord a
                            => [(a, CoreExpr a)]
                            -> [(CoreExpr a, a, [a])]
computePreliminaryStructure b =
  map (third (toList . intersection boundVariables)) bFV
  where
    boundVariables = fromList $ map fst b
    bFV = map (\(x, e) -> (e, x, freeVars e)) b

dependencyGraph :: Ord a => [(CoreExpr a, a, [a])] -> (Graph, DAGraphMap a)
dependencyGraph = dropThird . graphFromEdges

classifySCCs :: Eq a => DAGraphMap a -> [SCC Vertex] -> [Classification a]
classifySCCs dagMap = map (classify dagMap . flattenSCC)

classify :: Eq a => DAGraphMap a -> [Vertex] -> Classification a
classify dagMap []  = error "cannot have empty SCC"
classify dagMap [v] | x `elem` xs = ClRecursive [BinderB x e]
                    | otherwise = ClNonRecursive (BinderB x e)
  where (e, x, xs) = dagMap v
classify dagMap scc =
  ClRecursive $ map (uncurry BinderB . swap . dropThird . dagMap) scc
