/*
 *  CPAchecker is a tool for configurable software verification.
 *  This file is part of CPAchecker.
 *
 *  Copyright (C) 2007-2015  Dirk Beyer
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
package org.sosy_lab.cpachecker.cpa.bam.incremental;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.sosy_lab.common.Triple;
import org.sosy_lab.cpachecker.cfa.blocks.Block;
import org.sosy_lab.cpachecker.cfa.model.FunctionEntryNode;
import org.sosy_lab.cpachecker.cfa.model.FunctionExitNode;
import org.sosy_lab.cpachecker.core.interfaces.AbstractState;
import org.sosy_lab.cpachecker.core.interfaces.Precision;
import org.sosy_lab.cpachecker.core.reachedset.ReachedSet;
import org.sosy_lab.cpachecker.cpa.arg.ARGReachedSet;
import org.sosy_lab.cpachecker.cpa.arg.ARGState;

public class RefineHelper {
  private static RefineHelper instance;

  private List<Triple<AbstractState, Precision, Block>> curPrecisionFileCacheList = new ArrayList<>();
  private Map<AbstractState, Triple<AbstractState, Precision, Block>> curPrecisionFileCacheMap = new HashMap<>();
  private Map<ARGState, ARGState> backwardStateToStateMap = new HashMap<>();
  private Map<ARGState, ARGReachedSet> stateToReachedSetMap = new HashMap<>();
  private Map<AbstractState, AbstractState> replaceMap = new HashMap<>();

  private Map<ARGState, ARGState> newFlowBackwordStateToStateMap = new HashMap<>();
  private Map<ARGState, ARGReachedSet> newFlowStateToReachedSetMap = new HashMap<>();

  private boolean isRetFromMiddle = false;

  private Set<ARGState> canRerun = new HashSet<>();

  private RefineHelper() {

  }

  public static RefineHelper getInstance() {
    if(instance == null) {
      instance = new RefineHelper();
    }
    return instance;
  }

  public static boolean isReusedFileCache(ReachedSet reachedSet) {
    //the depth is two
    ARGState firstState = (ARGState)reachedSet.getFirstState();
    Collection<ARGState> childsState = firstState.getChildren();
    for(ARGState curState : childsState) {
      if(curState.getChildren().size() > 0) {
        return false;
      }
    }

    if(OneFileStore.getCfaNode((ARGState)reachedSet.getFirstState()) instanceof FunctionEntryNode) {
      if(OneFileStore.getCfaNode((ARGState)reachedSet.getLastState()) instanceof FunctionExitNode) {
        return true;
      }
    }
    return false;
  }

  public void buildCurPrecisionFileCacheMap() {
    for(Triple<AbstractState, Precision, Block> curTriple : curPrecisionFileCacheList) {
      AbstractState inputState = curTriple.getFirst();
      Collection<ARGState> childStates = ((ARGState)inputState).getChildren();
      for(ARGState curState : childStates) {
        curPrecisionFileCacheMap.put(curState, curTriple);
      }
    }
  }

  public void clearAll() {
    curPrecisionFileCacheList.clear();
    curPrecisionFileCacheMap.clear();
    backwardStateToStateMap.clear();
    stateToReachedSetMap.clear();
    replaceMap.clear();
//    canRerun.clear();
  }


  public List<Triple<AbstractState, Precision, Block>> getCurPrecisionFileCacheList() {
    return curPrecisionFileCacheList;
  }


  public void setCurPrecisionFileCacheList(List<Triple<AbstractState, Precision, Block>> pCurPrecisionFileCacheList) {
    curPrecisionFileCacheList = pCurPrecisionFileCacheList;
  }


  public Map<AbstractState, Triple<AbstractState, Precision, Block>> getCurPrecisionFileCacheMap() {
    return curPrecisionFileCacheMap;
  }


  public void setCurPrecisionFileCacheMap(
      Map<AbstractState, Triple<AbstractState, Precision, Block>> pCurPrecisionFileCacheMap) {
    curPrecisionFileCacheMap = pCurPrecisionFileCacheMap;
  }


  public Map<ARGState, ARGState> getBackwardStateToStateMap() {
    return backwardStateToStateMap;
  }


  public void setBackwardStateToStateMap(Map<ARGState, ARGState> pBackwardStateToStateMap) {
    backwardStateToStateMap = pBackwardStateToStateMap;
  }


  public Map<ARGState, ARGReachedSet> getStateToReachedSetMap() {
    return stateToReachedSetMap;
  }


  public void setStateToReachedSetMap(Map<ARGState, ARGReachedSet> pStateToReachedSetMap) {
    stateToReachedSetMap = pStateToReachedSetMap;
  }


  public Map<AbstractState, AbstractState> getReplaceMap() {
    return replaceMap;
  }


  public void setReplaceMap(Map<AbstractState, AbstractState> pReplaceMap) {
    replaceMap = pReplaceMap;
  }


  public boolean isRetFromMiddle() {
    return isRetFromMiddle;
  }


  public void setRetFromMiddle(boolean pIsRetFromMiddle) {
    isRetFromMiddle = pIsRetFromMiddle;
  }


  public Map<ARGState, ARGState> getNewFlowBackwordStateToStateMap() {
    return newFlowBackwordStateToStateMap;
  }


  public void setNewFlowBackwordStateToStateMap(Map<ARGState, ARGState> pNewFlowBackwordStateToStateMap) {
    newFlowBackwordStateToStateMap = pNewFlowBackwordStateToStateMap;
  }


  public Map<ARGState, ARGReachedSet> getNewFlowStateToReachedSetMap() {
    return newFlowStateToReachedSetMap;
  }


  public void setNewFlowStateToReachedSetMap(Map<ARGState, ARGReachedSet> pNewFlowStateToReachedSetMap) {
    newFlowStateToReachedSetMap = pNewFlowStateToReachedSetMap;
  }


  public Set<ARGState> getCanRerun() {
    return canRerun;
  }


  public void setCanRerun(Set<ARGState> pCanRerun) {
    canRerun = pCanRerun;
  }

}
