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
package org.sosy_lab.cpachecker.cpa.value.refiner.utils;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.List;
import java.util.Set;
import java.util.logging.Level;

import org.sosy_lab.common.Pair;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.cpachecker.cfa.CFA;
import org.sosy_lab.cpachecker.cfa.model.CFAEdge;
import org.sosy_lab.cpachecker.cfa.model.CFAEdgeType;
import org.sosy_lab.cpachecker.cfa.model.FunctionExitNode;
import org.sosy_lab.cpachecker.core.defaults.VariableTrackingPrecision;
import org.sosy_lab.cpachecker.cpa.arg.ARGPath;
import org.sosy_lab.cpachecker.cpa.arg.ARGPath.PathIterator;
import org.sosy_lab.cpachecker.cpa.arg.MutableARGPath;
import org.sosy_lab.cpachecker.cpa.conditions.path.AssignmentsInPathCondition.UniqueAssignmentsInPathConditionState;
import org.sosy_lab.cpachecker.cpa.value.ValueAnalysisCPA;
import org.sosy_lab.cpachecker.cpa.value.ValueAnalysisState;
import org.sosy_lab.cpachecker.cpa.value.ValueAnalysisTransferRelation;
import org.sosy_lab.cpachecker.exceptions.CPAException;
import org.sosy_lab.cpachecker.exceptions.CPATransferException;
import org.sosy_lab.cpachecker.util.AbstractStates;
import org.sosy_lab.cpachecker.util.states.MemoryLocation;

import com.google.common.collect.Iterables;

public class ValueAnalysisFeasibilityChecker {

  private final LogManager logger;
  private final ValueAnalysisTransferRelation transfer;
  private final VariableTrackingPrecision precision;

  /**
   * This method acts as the constructor of the class.
   *
   * @param pLogger the logger to use
   * @param pCfa the cfa in use
   * @param pInitial the initial state for starting the exploration
   * @throws InvalidConfigurationException
   */
  public ValueAnalysisFeasibilityChecker(LogManager pLogger, CFA pCfa, Configuration config) throws InvalidConfigurationException {
    logger    = pLogger;

    transfer  = new ValueAnalysisTransferRelation(Configuration.builder().build(), pLogger, pCfa);
    precision = VariableTrackingPrecision.createStaticPrecision(config, pCfa.getVarClassification(), ValueAnalysisCPA.class);
  }

  /**
   * This method checks if the given path is feasible, when not tracking the given set of variables.
   *
   * @param path the path to check
   * @return true, if the path is feasible, else false
   * @throws CPAException
   * @throws InterruptedException
   */
  public boolean isFeasible(final ARGPath path) throws CPAException, InterruptedException {
    return isFeasible(path, new ValueAnalysisState(), new ArrayDeque<ValueAnalysisState>());
  }

  /**
   * This method checks if the given path is feasible, starting with the given initial state.
   *
   * @param path the path to check
   * @param pInitial the initial state
   * @param pCallstack the initial callstack
   * @return true, if the path is feasible, else false
   * @throws CPAException
   * @throws InterruptedException
   */
  public boolean isFeasible(final ARGPath path, final ValueAnalysisState pInitial)
          throws CPAException, InterruptedException {
    return isFeasible(path, pInitial, new ArrayDeque<ValueAnalysisState>());
  }

  /**
   * This method checks if the given path is feasible, starting with the given initial state.
   *
   * @param path the path to check
   * @param pInitial the initial state
   * @param pCallstack the initial callstack
   * @return true, if the path is feasible, else false
   * @throws CPAException
   * @throws InterruptedException
   */
  public boolean isFeasible(final ARGPath path, final ValueAnalysisState pInitial, final Deque<ValueAnalysisState> pCallstack)
      throws CPAException, InterruptedException {
//    System.out.println("In value analysis feasible.");
//    System.out.println(path);
//    System.out.println();

    boolean performAbstraction = precision.allowsAbstraction();

    Set<MemoryLocation> exceedingMemoryLocations = obtainExceedingMemoryLocations(path);

    try {
      MutableARGPath currentPrefix = new MutableARGPath();
      ValueAnalysisState next = ValueAnalysisState.copyOf(pInitial);

      PathIterator iterator = path.pathIterator();
      while (iterator.hasNext()) {
        final CFAEdge edge = iterator.getOutgoingEdge();
//        System.out.println(edge);

        // we enter a function, so lets add the previous state to the stack
        if (edge.getEdgeType() == CFAEdgeType.FunctionCallEdge) {
          pCallstack.addLast(next);
        }

        // we leave a function, so rebuild return-state before assigning the return-value.
        if (!pCallstack.isEmpty() && edge.getEdgeType() == CFAEdgeType.FunctionReturnEdge) {
          // rebuild states with info from previous state
          final ValueAnalysisState callState = pCallstack.removeLast();
          next = next.rebuildStateAfterFunctionCall(callState, (FunctionExitNode)edge.getPredecessor());
        }

        Collection<ValueAnalysisState> successors = transfer.getAbstractSuccessorsForEdge(
            next,
            precision,
            edge);

        currentPrefix.addLast(Pair.of(iterator.getAbstractState(), iterator.getOutgoingEdge()));

        // no successors => path is infeasible
        if (successors.isEmpty()) {
          logger.log(Level.FINE, "found path to be infeasible: ", iterator.getOutgoingEdge(), " did not yield a successor");

          return false;
        }

        // extract singleton successor state
        next = Iterables.getOnlyElement(successors);

        // some variables might be blacklisted or tracked by BDDs
        // so perform abstraction computation here
        if(performAbstraction) {
          for (MemoryLocation memoryLocation : next.getTrackedMemoryLocations()) {
            if (!precision.isTracking(memoryLocation,
                next.getTypeForMemoryLocation(memoryLocation),
                iterator.getOutgoingEdge().getSuccessor())) {
              next.forget(memoryLocation);
            }
          }
        }

        for(MemoryLocation exceedingMemoryLocation : exceedingMemoryLocations) {
          next.forget(exceedingMemoryLocation);
        }

        iterator.advance();
      }

      return true;
    } catch (CPATransferException e) {
      throw new CPAException("Computation of successor failed for checking path: " + e.getMessage(), e);
    }
  }

  private Set<MemoryLocation> obtainExceedingMemoryLocations(ARGPath path) {
    UniqueAssignmentsInPathConditionState assignments =
        AbstractStates.extractStateByType(path.getLastState(),
        UniqueAssignmentsInPathConditionState.class);

    if(assignments == null) {
      return Collections.emptySet();
    }

    return assignments.getMemoryLocationsExceedingHardThreshold();
  }

  public List<Pair<ValueAnalysisState, CFAEdge>> evaluate(final ARGPath path)
      throws CPAException {

    try {
      List<Pair<ValueAnalysisState, CFAEdge>> reevaluatedPath = new ArrayList<>();
      ValueAnalysisState next = new ValueAnalysisState();

      PathIterator iterator = path.pathIterator();
      while (iterator.hasNext()) {
        Collection<ValueAnalysisState> successors = transfer.getAbstractSuccessorsForEdge(
            next,
            precision,
            iterator.getOutgoingEdge());

        if(successors.isEmpty()) {
          return reevaluatedPath;
        }

        // extract singleton successor state
        next = Iterables.getOnlyElement(successors);

        reevaluatedPath.add(Pair.of(next, iterator.getOutgoingEdge()));

        iterator.advance();
      }

      return reevaluatedPath;
    } catch (CPATransferException e) {
      throw new CPAException("Computation of successor failed for checking path: " + e.getMessage(), e);
    }
  }
}
