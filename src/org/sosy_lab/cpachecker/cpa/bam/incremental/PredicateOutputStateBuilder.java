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
import java.util.Set;
import java.util.SortedSet;

import org.sosy_lab.common.collect.PersistentMap;
import org.sosy_lab.cpachecker.cfa.model.CFANode;
import org.sosy_lab.cpachecker.cfa.types.c.CNumericTypes;
import org.sosy_lab.cpachecker.cfa.types.c.CType;
import org.sosy_lab.cpachecker.core.interfaces.AbstractState;
import org.sosy_lab.cpachecker.cpa.arg.ARGState;
import org.sosy_lab.cpachecker.cpa.automaton.AutomatonState;
import org.sosy_lab.cpachecker.cpa.callstack.CallstackState;
import org.sosy_lab.cpachecker.cpa.composite.CompositeState;
import org.sosy_lab.cpachecker.cpa.functionpointer.FunctionPointerState;
import org.sosy_lab.cpachecker.cpa.location.LocationState;
import org.sosy_lab.cpachecker.cpa.predicate.PredicateAbstractState;
import org.sosy_lab.cpachecker.util.AbstractStates;
import org.sosy_lab.cpachecker.util.globalinfo.GlobalInfo;
import org.sosy_lab.cpachecker.util.predicates.AbstractionFormula;
import org.sosy_lab.cpachecker.util.predicates.AbstractionManager;
import org.sosy_lab.cpachecker.util.predicates.interfaces.BooleanFormula;
import org.sosy_lab.cpachecker.util.predicates.interfaces.Region;
import org.sosy_lab.cpachecker.util.predicates.interfaces.view.FormulaManagerView;
import org.sosy_lab.cpachecker.util.predicates.pathformula.PathFormula;
import org.sosy_lab.cpachecker.util.predicates.pathformula.SSAMap;
import org.sosy_lab.cpachecker.util.predicates.pathformula.SSAMap.SSAMapBuilder;

public class PredicateOutputStateBuilder implements OutputStateBuilder {

  @Override
  public Collection<AbstractState> buildOutputState(ARGState pInputState, Collection<AbstractState> pOutputStates) {
    List<AbstractState> targetStates = new ArrayList<>();
    Iterator<AbstractState> iterator = pOutputStates.iterator();
    if(pOutputStates.size() > 1) {
      System.out.println("output states larger than 1......");
    }

    AbstractionManager abstractionManager = GlobalInfo.getInstance().getAbstractionManager();
    FormulaManagerView formulaManagerView = GlobalInfo.getInstance().getFormulaManagerView();
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

      PredicateAbstractState predicateAbstractState = AbstractStates.extractStateByType(pInputState, PredicateAbstractState.class);
      PredicateAbstractState cachePredicateAbstractState = (PredicateAbstractState) iterator.next();
      BooleanFormula formula = cachePredicateAbstractState.getAbstractionFormula().asFormula();
      Region region = abstractionManager.buildRegionFromFormula(formula);
      SSAMap inputSSAMAP = predicateAbstractState.getAbstractionFormula().getBlockFormula().getSsa();
      Set<String> variableNames = formulaManagerView.extractVariableNames(formula);
      SSAMap outputSSAMAP = buildOutputStateSSAMap(inputSSAMAP, cachePredicateAbstractState.getAbstractionFormula().getBlockFormula().getSsa(), variableNames);
      BooleanFormula instantiatedFormula = formulaManagerView.instantiate(formula, outputSSAMAP);

      PathFormula pathFormula0 = cachePredicateAbstractState.getAbstractionFormula().getBlockFormula();

      PathFormula pathFormula = new PathFormula(pathFormula0.getFormula(), outputSSAMAP, pathFormula0.getPointerTargetSet(), pathFormula0.getLength());

      Set<Integer> reuseIds = predicateAbstractState.getAbstractionFormula().getIdsOfStoredAbstractionReused();
      AbstractionFormula abstractionFormula = new AbstractionFormula(formulaManagerView, region, formula, instantiatedFormula, pathFormula, reuseIds);

      PersistentMap<CFANode, Integer> abstractionLocationPaths = predicateAbstractState.getAbstractionLocationsOnPath().putAndCopy(exitLocationState.getLocationNode(), 1);
      PathFormula outOldPathFormula = predicateAbstractState.getPathFormula();
      PathFormula outPathFormula = new PathFormula(outOldPathFormula.getFormula(), outputSSAMAP, outOldPathFormula.getPointerTargetSet(), outOldPathFormula.getLength());
      PredicateAbstractState newPredicateAbstractState = PredicateAbstractState.mkAbstractionState(outPathFormula, abstractionFormula, abstractionLocationPaths);
      elements.add(newPredicateAbstractState);

      AutomatonState automatonState = AbstractStates.extractStateByType(pInputState, AutomatonState.class);
      elements.add(automatonState);

      CompositeState pWrappedState = new CompositeState(elements);
      ARGState targetState = new ARGState(pWrappedState, pInputState);
      targetState.addParent(pInputState);
      targetStates.add(targetState);
    }
    return targetStates;
  }

  private SSAMap buildOutputStateSSAMap(SSAMap inputSSAMap, SSAMap cachedSSAMAP, Set<String> variableNames) {
    SSAMapBuilder builder = SSAMap.emptySSAMap().builder();
    SortedSet<String> variables = inputSSAMap.allVariables();
    for(String curV : variables) {
      builder.setIndex(curV, inputSSAMap.getType(curV), inputSSAMap.getIndex(curV) + 1);
    }
    for(String curV : variableNames) {
      if(!variables.contains(curV)) {
        CType variableType = cachedSSAMAP.getType(curV);
        if(variableType == null) {
          variableType = CNumericTypes.INT;
        }
        builder.setIndex(curV, variableType, 2);
      }
    }
    return builder.build();
  }

}
