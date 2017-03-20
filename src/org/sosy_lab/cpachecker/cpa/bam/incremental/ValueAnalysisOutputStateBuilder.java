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
import java.util.Iterator;
import java.util.List;

import org.sosy_lab.cpachecker.cfa.model.CFANode;
import org.sosy_lab.cpachecker.core.interfaces.AbstractState;
import org.sosy_lab.cpachecker.cpa.arg.ARGState;
import org.sosy_lab.cpachecker.cpa.automaton.AutomatonState;
import org.sosy_lab.cpachecker.cpa.callstack.CallstackState;
import org.sosy_lab.cpachecker.cpa.composite.CompositeState;
import org.sosy_lab.cpachecker.cpa.functionpointer.FunctionPointerState;
import org.sosy_lab.cpachecker.cpa.location.LocationState;
import org.sosy_lab.cpachecker.cpa.value.ValueAnalysisState;
import org.sosy_lab.cpachecker.util.AbstractStates;

public class ValueAnalysisOutputStateBuilder implements OutputStateBuilder {
  @Override
  public Collection<AbstractState> buildOutputState(final ARGState pInputState, Collection<AbstractState> pOutputStates) {
    List<AbstractState> targetStates = new ArrayList<>();
    Iterator<AbstractState> iterator = pOutputStates.iterator();
    if(pOutputStates.size() == 2) {
      iterator.next();
    }
    while(iterator.hasNext()) {
      List<AbstractState> elements = new ArrayList<>();
      LocationState locationState = AbstractStates.extractStateByType(pInputState, LocationState.class);
      CFANode node = locationState.getLocationNode();
      int id = node.getNodeNumber() - 1;
      LocationState exitLocationState = LocationState.getLocationStateByID(id, node);
      elements.add(exitLocationState);

      CallstackState callstackState = AbstractStates.extractStateByType(pInputState, CallstackState.class);
      elements.add(callstackState);
      FunctionPointerState functionPointerState = AbstractStates.extractStateByType(pInputState, FunctionPointerState.class);
      elements.add(functionPointerState);

      ValueAnalysisState valueAnalysisState = AbstractStates.extractStateByType(pInputState, ValueAnalysisState.class);
      ValueAnalysisState cacheValueAnalysisState = (ValueAnalysisState)iterator.next();
      ValueAnalysisState newValueAnalysisState = new ValueAnalysisState(cacheValueAnalysisState.getConstantsMap1(), valueAnalysisState.getMemLocToType());
      elements.add(newValueAnalysisState);

      AutomatonState automatonState = AbstractStates.extractStateByType(pInputState, AutomatonState.class);
      elements.add(automatonState);

      CompositeState pWrappedState = new CompositeState(elements);
      ARGState targetState = new ARGState(pWrappedState, pInputState);
      targetState.addParent(pInputState);
      targetStates.add(targetState);
    }
    return targetStates;
  }
}
