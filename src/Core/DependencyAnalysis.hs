{- Dependency analysis

   Core-to-Core transformation with the goal of simplifying letrec
   expressions by detecting minimal sets of mutually recursive
   definitions and eliminating redundant uses of the construct
   in non-recursive bindings by transforming them into normal let
   expressions.
-}

module Core.DependencyAnalysis where
