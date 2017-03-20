/*
 *  CPAchecker is a tool for configurable software verification.
 *  This file is part of CPAchecker.
 *
 *  Copyright (C) 2007-2014  Dirk Beyer
 *  All rights reserved.
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 *
 *
 *  CPAchecker web page:
 *    http://cpachecker.sosy-lab.org
 */
package org.sosy_lab.cpachecker.cpa.bam;

import static org.sosy_lab.cpachecker.cpa.bam.AbstractBAMBasedRefiner.DUMMY_STATE_FOR_MISSING_BLOCK;
import static org.sosy_lab.cpachecker.util.AbstractStates.extractLocation;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.NavigableSet;
import java.util.Set;
import java.util.TreeSet;
import java.util.logging.Level;

import org.sosy_lab.common.Triple;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.cpachecker.cfa.blocks.Block;
import org.sosy_lab.cpachecker.cfa.blocks.BlockPartitioning;
import org.sosy_lab.cpachecker.cfa.model.CFAEdge;
import org.sosy_lab.cpachecker.cfa.model.CFANode;
import org.sosy_lab.cpachecker.cfa.model.MultiEdge;
import org.sosy_lab.cpachecker.cmdline.CPAMain;
import org.sosy_lab.cpachecker.core.interfaces.AbstractState;
import org.sosy_lab.cpachecker.core.interfaces.Precision;
import org.sosy_lab.cpachecker.core.interfaces.Reducer;
import org.sosy_lab.cpachecker.core.reachedset.ReachedSet;
import org.sosy_lab.cpachecker.cpa.arg.ARGReachedSet;
import org.sosy_lab.cpachecker.cpa.arg.ARGState;
import org.sosy_lab.cpachecker.cpa.bam.incremental.EqualHelpState;
import org.sosy_lab.cpachecker.cpa.bam.incremental.IncrementalCache;
import org.sosy_lab.cpachecker.cpa.bam.incremental.OneFileStore;
import org.sosy_lab.cpachecker.cpa.bam.incremental.RefineHelper;
import org.sosy_lab.cpachecker.exceptions.CPAException;
import org.sosy_lab.cpachecker.util.AbstractStates;

public class BAMCEXSubgraphComputer {

  private final BlockPartitioning partitioning;
  private final Reducer reducer;
  private final BAMCache bamCache;
  private final Map<ARGState, ARGState> pathStateToReachedState;
  private final Map<AbstractState, ReachedSet> abstractStateToReachedSet;
  private final Map<AbstractState, AbstractState> expandedToReducedCache;
  private final LogManager logger;

  private final BAMTransferRelation transferRelation;

  BAMCEXSubgraphComputer(BlockPartitioning partitioning, Reducer reducer, BAMCache bamCache,
                         Map<ARGState, ARGState> pathStateToReachedState,
                         Map<AbstractState, ReachedSet> abstractStateToReachedSet,
                         Map<AbstractState, AbstractState> expandedToReducedCache,
                         LogManager logger) {
    this.partitioning = partitioning;
    this.reducer = reducer;
    this.bamCache = bamCache;
    this.pathStateToReachedState = pathStateToReachedState;
    this.abstractStateToReachedSet = abstractStateToReachedSet;
    this.expandedToReducedCache = expandedToReducedCache;
    this.logger = logger;
    transferRelation = null;
  }

  BAMCEXSubgraphComputer(BlockPartitioning partitioning, Reducer reducer, BAMCache bamCache,
                        Map<ARGState, ARGState> pathStateToReachedState,
                        Map<AbstractState, ReachedSet> abstractStateToReachedSet,
                        Map<AbstractState, AbstractState> expandedToReducedCache,
                        LogManager logger, BAMTransferRelation bamTransferRelation) {
    this.partitioning = partitioning;
    this.reducer = reducer;
    this.bamCache = bamCache;
    this.pathStateToReachedState = pathStateToReachedState;
    this.abstractStateToReachedSet = abstractStateToReachedSet;
    this.expandedToReducedCache = expandedToReducedCache;
    this.logger = logger;
    transferRelation = bamTransferRelation;
  }

  public void rerunFileCachedFun(Triple<AbstractState, Precision, Block> triple, ARGReachedSet reachedSet) throws CPAException, InterruptedException {
    IncrementalCache.getInstance().setCanUseFileCache(false);
    System.out.println("start rerun fun.......");

    AbstractState initialState = triple.getFirst();
    ReachedSet curReachedSet = abstractStateToReachedSet.get(initialState);
//    abstractStateToReachedSet.remove(initialState);

    if(curReachedSet.getLastState() != null) {
      //remove outout state
      ARGState firstState = (ARGState)curReachedSet.getFirstState();
      Collection<ARGState> removeChildStates = firstState.getChildren();
      for(ARGState curC : removeChildStates) {
        curReachedSet.remove(curC);
      }
      List<ARGState> tmpList = new ArrayList<>(removeChildStates);
      for(ARGState tmpState : tmpList) {
        tmpState.removeFromARG();
      }
    }

    CFANode node = AbstractStates.extractLocation(initialState);
    Block block = partitioning.getBlockForCallNode(node);
    Precision initialPrecision = triple.getSecond();
    Precision reducedPrecision = curReachedSet.getPrecision(curReachedSet.getFirstState());

    Block tmpBlock = transferRelation.getCurrentBlock();
    transferRelation.setCurrentBlock(block);
    transferRelation.analyseBlockAndExpand(initialState, initialPrecision, triple.getThird(), curReachedSet.getFirstState(), reducedPrecision);
    transferRelation.setCurrentBlock(tmpBlock);

  //change return node to new create node
    Collection<ARGState> childStates = ((ARGState)initialState).getChildren();

    if(childStates.size() != 2) {
      System.out.println("child size larger than 1......." + childStates.size());
    }
    List<ARGState> childList = new ArrayList<>(childStates);
    int childSize = childList.size();
    int halfSize = childSize / 2;
    for(int i = 0; i < halfSize; i++) {
      ARGState toReplaceState = childList.get(i);
      ARGState replaceState = null;
      if(childSize % 2 != 0) {
        replaceState = getReplaceState(toReplaceState, childList, block.getFunctionName());
      } else {
        replaceState = childList.get(halfSize + i);
      }
      assert replaceState != null;
      Collection<ARGState> nextStates = toReplaceState.getChildren();
      for(ARGState nextState : nextStates) {
        nextState.addParent(replaceState);
      }
      toReplaceState.removeFromARG();
      reachedSet.replaceReachedState(toReplaceState, replaceState);
      RefineHelper.getInstance().getReplaceMap().put(toReplaceState, replaceState);
    }

    System.out.println("end rerun fun......");
    IncrementalCache.getInstance().setCanUseFileCache(true);
  }

  private ARGState getReplaceState(ARGState toReplaceState, List<ARGState> childList, String funName) {
    EqualHelpState helpState1 = EqualHelpState.buildEqualHelpState(OneFileStore.getRealState(toReplaceState), funName);
    for(int i = childList.size() / 2; i < childList.size(); i++) {
      EqualHelpState helpState2 = EqualHelpState.buildEqualHelpState(OneFileStore.getRealState(childList.get(i)), funName);
      if(helpState1.equals(helpState2)) {
        return childList.get(i);
      }
    }
    System.out.println("get replace state null......");
    return null;
  }

  /** returns the root of a subtree, leading from the root element of the given reachedSet to the target state.
   * The subtree is represented using children and parents of ARGElements,
   * where newTreeTarget is the ARGState in the constructed subtree that represents target.
   *
   * If the target is reachable via a missing block (aka "hole"),
   * the DUMMY_STATE_FOR_MISSING_BLOCK is returned.
   * Then we expect, that the next actions are removing cache-entries from bam-cache,
   * updating some waitlists and restarting the CPA-algorithm, so that the missing block is analyzed again.
   *
   * @param target a state from the reachedSet, is used as the last state of the returned subgraph.
   * @param reachedSet contains the target-state.
   * @param newTreeTarget a copy of the target, should contain the same information as target.
   *
   * @return root of a subgraph, that contains all states on all paths to newTreeTarget.
   *         The subgraph contains only copies of the real ARG states,
   *         because one real state can be used multiple times in one path.
   *         The map "pathStateToReachedState" should be used to search the correct real state.
   */
  BackwardARGState computeCounterexampleSubgraph(ARGState target,
      ARGReachedSet reachedSet, BackwardARGState newTreeTarget) {
    assert reachedSet.asReachedSet().contains(target);

    //start by creating ARGElements for each node needed in the tree
    final Map<ARGState, BackwardARGState> finishedStates = new HashMap<>();
    final NavigableSet<ARGState> waitlist = new TreeSet<>(); // for sorted IDs in ARGstates
    BackwardARGState root = null;

    //changed begin of flow
//    if(CPAMain.isReuseSummary) {
//        if(RefineHelper.getInstance().getCurPrecisionFileCacheMap().containsKey(target)) {
//          Triple<AbstractState, Precision, Block> curTriple = RefineHelper.getInstance().getCurPrecisionFileCacheMap().get(target);
//          try {
//            rerunFileCachedFun(curTriple, reachedSet);
//          } catch (CPAException | InterruptedException e) {
//            // TODO Auto-generated catch block
//            e.printStackTrace();
//          }
//          assert RefineHelper.getInstance().getReplaceMap().containsKey(target);
//          AbstractState replaceState = RefineHelper.getInstance().getReplaceMap().get(target);
//          target = (ARGState)replaceState;
//          newTreeTarget = new BackwardARGState(target);
//      }
//    }

    pathStateToReachedState.put(newTreeTarget, target);
    finishedStates.put(target, newTreeTarget);
    waitlist.addAll(target.getParents()); // add parent for further processing
    while (!waitlist.isEmpty()) {
      ARGState currentState = waitlist.pollLast(); // get state with biggest ID

      if(CPAMain.isReuseSummary) {
        if(RefineHelper.getInstance().getCurPrecisionFileCacheMap().containsKey(currentState)) {
          Triple<AbstractState, Precision, Block> curTriple = RefineHelper.getInstance().getCurPrecisionFileCacheMap().get(currentState);
          try {
            rerunFileCachedFun(curTriple, reachedSet);
          } catch (CPAException | InterruptedException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
          }
          assert RefineHelper.getInstance().getReplaceMap().containsKey(currentState);
          AbstractState replaceState = RefineHelper.getInstance().getReplaceMap().get(currentState);
          currentState = (ARGState)replaceState;
          RefineHelper.getInstance().getCurPrecisionFileCacheMap().remove(currentState);
      }
    }

      assert reachedSet.asReachedSet().contains(currentState);

      if (finishedStates.containsKey(currentState)) {
        continue; // state already done
      }

      final BackwardARGState newCurrentState = new BackwardARGState(currentState);
      finishedStates.put(currentState, newCurrentState);
      pathStateToReachedState.put(newCurrentState, currentState);

//      RefineHelper.getInstance().getNewFlowBackwordStateToStateMap().put(newCurrentState, currentState);
//      RefineHelper.getInstance().getNewFlowStateToReachedSetMap().put(currentState, reachedSet);

      //changed by CLM
      if(CPAMain.isReuseSummary) {
        if(RefineHelper.getInstance().getCurPrecisionFileCacheMap().containsKey(currentState)) {
          RefineHelper.getInstance().getBackwardStateToStateMap().put(newCurrentState, currentState);
          RefineHelper.getInstance().getStateToReachedSetMap().put(currentState, reachedSet);
        }
      }

      // add parent for further processing
      waitlist.addAll(currentState.getParents());
//System.out.println("curstate:" + currentState);
      for (final ARGState child : currentState.getChildren()) {
        if (!finishedStates.containsKey(child)) {
          // child is not in the subgraph, that leads to the target,so ignore it.
          // because of the ordering, all important children should be finished already.
          continue;
        }

        final BackwardARGState newChild = finishedStates.get(child);

        if (expandedToReducedCache.containsKey(child)) {
          // If child-state is an expanded state, we are at the exit-location of a block.
          // In this case, we enter the block (backwards).
          // We must use a cached reachedSet to process further, because the block has its own reachedSet.
          // The returned 'innerTree' is the rootNode of the subtree, created from the cached reachedSet.
          // The current subtree (successors of child) is appended beyond the innerTree, to get a complete subgraph.
          final ARGState reducedTarget = (ARGState) expandedToReducedCache.get(child);
          BackwardARGState innerTree = computeCounterexampleSubgraphForBlock(currentState, reducedTarget, newChild);
          if (innerTree == DUMMY_STATE_FOR_MISSING_BLOCK) {
            ARGSubtreeRemover.removeSubtree(reachedSet, currentState);
            System.out.println("dummy state................");
            return DUMMY_STATE_FOR_MISSING_BLOCK;
          }

          // reconnect ARG: replace the state 'innerTree' with the current state.
          for (ARGState innerChild : innerTree.getChildren()) {
            innerChild.addParent(newCurrentState);
          }
          innerTree.removeFromARG();

          assert pathStateToReachedState.containsKey(innerTree) : "root of subgraph was not finished";
          pathStateToReachedState.remove(innerTree); // not needed any more

          // now the complete inner tree (including all successors of the state innerTree on paths to reducedTarget)
          // is inserted between newCurrentState and child.

          assert pathStateToReachedState.containsKey(newChild) : "end of subgraph was not handled";
          assert pathStateToReachedState.get(newCurrentState) == currentState : "input-state must be from outer reachedset";

          // check that at block output locations the first reached state is used for the CEXsubgraph,
          // i.e. the reduced abstract state from the (most) inner block's reached set.
          ARGState matchingChild = (ARGState) expandedToReducedCache.get(child);
          while (expandedToReducedCache.containsKey(matchingChild)) {
            matchingChild = (ARGState) expandedToReducedCache.get(matchingChild);
          }
          assert pathStateToReachedState.get(newChild) == matchingChild : "output-state must be from (most) inner reachedset";

        } else {
          // child is a normal successor
          // -> create an simple connection from parent to current
          //changed by CLM
          //add a multiedge to function summary reuse.
          if(currentState.getEdgeToChild(child) == null) {
            addMultiEdge(currentState, child);
          }
          assert currentState.getEdgeToChild(child) != null: "unexpected ARG state: parent has no edge to child.";
          newChild.addParent(newCurrentState);
        }
      }

      if(CPAMain.isReuseSummary) {
        if(RefineHelper.getInstance().getCurPrecisionFileCacheMap().containsKey(currentState)) {
//          CFANode curNode = AbstractStates.extractLocation(currentState);
          if(!RefineHelper.getInstance().getCanRerun().contains(currentState)) {
            RefineHelper.getInstance().setRetFromMiddle(true);
            RefineHelper.getInstance().getCanRerun().add(currentState);
            return newCurrentState;
          }
        }
      }

      if (currentState.getParents().isEmpty()) {
        assert root == null : "root should not be set before";
        root = newCurrentState;
      }
    }
    assert root != null;
    return root;
  }

  private void addMultiEdge(ARGState fromState, ARGState toState) {
    CFANode fromNode = AbstractStates.extractLocation(fromState);
    CFANode toNode = AbstractStates.extractLocation(toState);
    List<CFAEdge> downEdges = new ArrayList<>();
    Set<CFANode> visitedSets = new HashSet<>();
    CFANode curNode = toNode;
    visitedSets.add(curNode);

//    Stack<CFANode> stack = new Stack<>();
//    stack.push(curNode);
//    while(!stack.isEmpty()) {
//      curNode = stack.pop();
//      int size = curNode.getNumLeavingEdges();
//      for(int i = 0; i < size; i++) {
//        CFAEdge curEdge = curNode.getLeavingEdge(i);
//        CFANode successor = curEdge.getSuccessor();
//        if(visitedSets.contains(successor)) {
//          continue;
//        }
//        visitedSets.add(successor);
//        downEdges.add(curEdge);
//        if(successor == toNode) {
//          break;
//        }
//        stack.push(successor);
//      }
//    }

    while(curNode != fromNode) {
      CFAEdge curEdge = curNode.getEnteringEdge(0);
      downEdges.add(curEdge);
      curNode = curEdge.getPredecessor();
      if(visitedSets.contains(curNode)) {
        break;
      } else {
        visitedSets.add(curNode);
      }
    }

    MultiEdge toAddEdge = new MultiEdge(fromNode, toNode, downEdges);
    fromNode.addLeavingEdge(toAddEdge);
    toNode.addEnteringEdge(toAddEdge);
  }

  /**
   * This method looks for the reached set that belongs to (root, rootPrecision),
   * then looks for target in this reached set and constructs a tree from root to target
   * (recursively, if needed).
   *
   * If the target is reachable via a missing block (aka "hole"),
   * the DUMMY_STATE_FOR_MISSING_BLOCK is returned.
   * Then we expect, that the next actions are removing cache-entries from bam-cache,
   * updating some waitlists and restarting the CPA-algorithm, so that the missing block is analyzed again.
   *
   * @param expandedRoot the expanded initial state of the reachedSet of current block
   * @param reducedTarget exit-state of the reachedSet of current block
   * @param newTreeTarget copy of the exit-state of the reachedSet of current block.
   *                     newTreeTarget has only children, that are all part of the Pseudo-ARG
   *                     (these children are copies of states from reachedSets of other blocks)
   *
   * @return the default return value is the rootState of the Pseudo-ARG.
   *         We return NULL, if reachedSet is invalid, i.e. there is a 'hole' in it,
   *         maybe because of a refinement of the block at another CEX-refinement.
   *         In that case we also perform some cleanup-operations.
   */
  public BackwardARGState computeCounterexampleSubgraphForBlock(
          final ARGState expandedRoot, final ARGState reducedTarget, final BackwardARGState newTreeTarget) {
    // first check, if the cached state is valid.
    if (reducedTarget.isDestroyed()) {
      logger.log(Level.FINE,
              "Target state refers to a destroyed ARGState, i.e., the cached subtree is outdated. Updating it.");
      return DUMMY_STATE_FOR_MISSING_BLOCK;
    }
//System.out.println("\n\ncompute counterexample subgraph for block, initial state:" + expandedRoot);
    // TODO why do we use 'abstractStateToReachedSet' to get the reachedSet and not 'bamCache'?
    final ReachedSet reachedSet = abstractStateToReachedSet.get(expandedRoot);

    // we found the reachedSet, corresponding to the root and precision.
    // now try to find the target in the reach set.
    assert reachedSet.contains(reducedTarget);

    // we found the target; now construct a subtree in the ARG starting with targetARGElement
    final BackwardARGState result = computeCounterexampleSubgraph(reducedTarget, new ARGReachedSet(reachedSet), newTreeTarget);
    if (result == DUMMY_STATE_FOR_MISSING_BLOCK) {
      //enforce recomputation to update cached subtree
      logger.log(Level.FINE,
              "Target state refers to a destroyed ARGState, i.e., the cached subtree will be removed.");

      // TODO why do we use precision of reachedSet from 'abstractStateToReachedSet' here and not the reduced precision?
      final CFANode rootNode = extractLocation(expandedRoot);
      final Block rootBlock = partitioning.getBlockForCallNode(rootNode);
      final AbstractState reducedRootState = reducer.getVariableReducedState(expandedRoot, rootBlock, rootNode);
      bamCache.removeReturnEntry(reducedRootState, reachedSet.getPrecision(reachedSet.getFirstState()), rootBlock);
    }
    return result;
  }


  /**
   * This is a ARGState, that counts backwards, used to build the Pseudo-ARG for CEX-retrieval.
   * As the Pseudo-ARG is build backwards starting at its end-state, we count the ID backwards.
   */
  public static class BackwardARGState extends ARGState {

    private static final long serialVersionUID = -3279533907385516993L;
    private int decreasingStateID;
    private static int nextDecreaseID = Integer.MAX_VALUE;

    public BackwardARGState(ARGState originalState) {
      super(originalState.getWrappedState(), null);
      decreasingStateID = nextDecreaseID--;
    }

    @Override
    public boolean isOlderThan(ARGState other) {
      if (other instanceof BackwardARGState) { return decreasingStateID < ((BackwardARGState) other).decreasingStateID; }
      return super.isOlderThan(other);
    }

    void updateDecreaseId() {
      decreasingStateID = nextDecreaseID--;
    }

    @Override
    public String toString() {
      return "BackwardARGState {{" + super.toString() + "}}";
    }
  }
}
