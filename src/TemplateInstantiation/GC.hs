module TemplateInstantiation.GC where

import Control.Monad
import TemplateInstantiation.Structures
import Heap
import Data.List (nub)
import Control.Monad.State

---------------------------------------
-- Data structure to handle node marking

data GCNode = Marked Node | Unmarked Node deriving (Eq, Show)
type GCHeap = Heap GCNode

nodeToGcNode :: Node -> GCNode
nodeToGcNode = Unmarked

gcNodeToNode :: GCNode -> Node
gcNodeToNode (Marked node) = node
gcNodeToNode (Unmarked node) = node

heapToGcHeap :: TiHeap -> GCHeap
heapToGcHeap = fmap nodeToGcNode

gcHeapToHeap :: GCHeap -> TiHeap
gcHeapToHeap = fmap gcNodeToNode

--------------------------------------------------------------------------------

gc :: TiState -> TiState
gc state = liftHeapFunc heapChanger state
  where
    addresses     = findStateRoots state
    gcHeapChanger = execState (forM_ addresses markFrom >> scanHeap)
    heapChanger   = gcHeapToHeap . gcHeapChanger . heapToGcHeap

--------------------------------------------------------------------------------

findStackRoots :: TiStack -> [Addr]
findStackRoots = id

findDumpRoots :: TiDump -> [Addr]
findDumpRoots = nub . concatMap findStackRoots

findGlobalRoots :: TiGlobals -> [Addr]
findGlobalRoots = map snd

findStateRoots :: TiState -> [Addr]
findStateRoots state = nub $ findStackRoots  (stack   state) ++
                             findDumpRoots   (dump    state) ++
                             findGlobalRoots (globals state)

--------------------------------------------------------------------------------
-- Mark phase

-- In the mark phase, each node whose address is in the machine state is marked.
-- When a node is marked, all its descendants are also marked, and so on
-- recursively.

-- markFrom returns a new heap in which all the nodes accessible from the given
-- address have been marked.

markFrom :: Addr -> HeapState GCNode ()
markFrom addr = do
  n <- hLookup' addr
  case n of
    Marked _ -> return ()
    Unmarked node -> hUpdate addr (Marked node) >> markFrom addr >> case node of
      NAp a1 a2 -> markFrom a1 >> markFrom a2
      NInd a    -> markFrom a
      _         -> return ()

--------------------------------------------------------------------------------
-- Scan phase

-- In the scan phase, all the nodes in the heap (whether marked or not) are
-- examined. Unmarked nodes are freed, and marked nodes are unmarked.

-- I would rather say, unmarked nodes are freed, and the rest is left as it is.

scanHeap :: HeapState GCNode ()
scanHeap = do
  addresses <- hAddresses'
  forM_ addresses scanNode
  where
    scanNode addr = hLookup' addr >>= \n -> case n of
      Unmarked _ -> hFree addr
      Marked _ -> return ()
