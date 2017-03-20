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

import java.io.DataInputStream;
import java.io.DataOutputStream;
import java.io.IOException;
import java.io.Writer;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Iterator;

import org.sosy_lab.cpachecker.cfa.blocks.Block;
import org.sosy_lab.cpachecker.cfa.model.CFANode;
import org.sosy_lab.cpachecker.cmdline.CPAMain;
import org.sosy_lab.cpachecker.core.interfaces.AbstractState;
import org.sosy_lab.cpachecker.cpa.arg.ARGState;
import org.sosy_lab.cpachecker.cpa.bam.incremental.program.FunctionInfo;
import org.sosy_lab.cpachecker.cpa.bam.incremental.program.ProgramInfo;
import org.sosy_lab.cpachecker.cpa.composite.CompositeState;
import org.sosy_lab.cpachecker.cpa.location.LocationState;
import org.sosy_lab.cpachecker.util.predicates.interfaces.FormulaManager;
import org.sosy_lab.cpachecker.util.predicates.pathformula.SSAMap;
import org.sosy_lab.cpachecker.util.predicates.smtInterpol.IOUtil;


public class OneFileStore {
  private String funName;
  private AbstractState inputState;
  private Collection<AbstractState> returnStates;
  private StoreHelper storeHelper;

  public static final String INPUTSTATEBEGIN = "ISB";
  public static final String INPUTSTATEEND = "ISE";
  public static final String OUTPUTSTATEBEGIN = "OSB";
  public static final String OUTPUTSTATEEND = "OSE";
  public static final String OTHERSBEGIN = "OTB";
  public static final String OTHERSEND = "OTE";

  public static final int SAVESUMMARYT=2;

  public OneFileStore(String funName, AbstractState inputState, Collection<AbstractState> outputState) {
    this.funName = funName;
    this.inputState = getRealState(inputState);
    returnStates = new ArrayList<>();
    for(AbstractState curState : outputState) {
      returnStates.add(getRealState(curState));
    }
    switch (CPAMain.abstractType) {
    case VALUEANALYSIS:
      storeHelper = new ValueAnalysisStoreHelper();
      break;
    case PREDICATEANALYSIS:
      storeHelper = new PredicateAnalysisStoreHelper();
      break;
    default:
      break;
    }
  }

  public void saveToFile(Writer writer) throws IOException {
   writer.append(INPUTSTATEBEGIN + "\n");
   writer.append(storeHelper.stateToString(inputState, funName) + "\n");
   writer.append(INPUTSTATEEND + "\n");
   Iterator<AbstractState> returnIterator = returnStates.iterator();
   while(returnIterator.hasNext()) {
     writer.append(OUTPUTSTATEBEGIN + "\n");
     writer.append(storeHelper.stateToString(returnIterator.next(), funName) + "\n");
     writer.append(OUTPUTSTATEEND + "\n");
   }
   writer.append(OTHERSBEGIN + "\n");
   String others = storeHelper.getOthers(inputState, returnStates);
   if(others != null && others.trim().length() > 0) {
     writer.append(others + "\n");
  }
   writer.append(OTHERSEND + "\n");
 }

  public void serialize(DataOutputStream out, FormulaManager manager) throws IOException {
    storeHelper.serializeOthers(inputState, returnStates, out, manager);
    storeHelper.serializeState(inputState, manager);
    int retSize = returnStates.size();
    IOUtil.writeVInt(out, retSize);
    Iterator<AbstractState> retIterator = returnStates.iterator();
    while(retIterator.hasNext()) {
      storeHelper.serializeState(retIterator.next(), manager);
    }
  }

  public static boolean canStore(Block block, AbstractState inputState) {
    ProgramInfo pInfo = ProgramInfo.getInstance();
    String funName = block.getFunctionName();
    FunctionInfo curInfo = pInfo.getNowFunctionInfo().get(funName);
    return !((ARGState)inputState).isTarget() &&
        (pInfo.getFuncLineMap(funName) >= SAVESUMMARYT || curInfo.getCalledFunctionName().size() >= 1
        || curInfo.getFunctionBody().contains("for(") || curInfo.getFunctionBody().contains("for (")
        || curInfo.getFunctionBody().contains("while(") || curInfo.getFunctionBody().contains("while ("));
  }

  public static AbstractState getRealState(AbstractState state) {
    StoreHelper storeHelper = null;
    switch (CPAMain.abstractType) {
    case VALUEANALYSIS:
      storeHelper = new ValueAnalysisStoreHelper();
      break;
    case PREDICATEANALYSIS:
      storeHelper = new PredicateAnalysisStoreHelper();
      break;
    default:
      break;
    }
    return storeHelper.getRealState(state);
  }

  public static int getCFANodeId(ARGState argState) {
    return getCfaNode(argState).getNodeNumber();
  }

  public static CFANode getCfaNode(ARGState argState) {
    CompositeState compositeState = (CompositeState)argState.getWrappedState();
    CFANode result = null;
    for(AbstractState curState : compositeState.getWrappedStates()) {
      if(curState instanceof LocationState) {
        result = ((LocationState)curState).getLocationNode();
        break;
      }
    }
    return result;
  }

  public static OneFileStore resolve(String funName, DataInputStream in, FormulaManager manager) throws IOException {
    StoreHelper storeHelper = null;
    switch (CPAMain.abstractType) {
    case VALUEANALYSIS:
      storeHelper = new ValueAnalysisStoreHelper();
      break;
    case PREDICATEANALYSIS:
      storeHelper = new PredicateAnalysisStoreHelper();
      break;
    default:
      break;
    }
    SSAMap ssaMap = storeHelper.resolveOthers(in, manager);
    AbstractState inputState = storeHelper.resolveState(funName, manager);
    int retSize = IOUtil.readVInt(in);
    Collection<AbstractState> returnStates = new ArrayList<>();
    for(int i = 0; i < retSize; i++) {
      AbstractState curState = storeHelper.resolveState(funName, manager, ssaMap);
      returnStates.add(curState);
    }
    return new OneFileStore(funName, inputState, returnStates);
  }

  public static OneFileStore buildFromString(String funName, String input, Collection<String> outputs, String others) {
    StoreHelper storeHelper = null;
    switch (CPAMain.abstractType) {
    case VALUEANALYSIS:
      storeHelper = new ValueAnalysisStoreHelper();
      break;
    case PREDICATEANALYSIS:
      storeHelper = new PredicateAnalysisStoreHelper();
      break;
    default:
      break;
    }
    AbstractState inputState = storeHelper.buildStateFromString(funName, input);
    Collection<AbstractState> returnStates = new ArrayList<>();
    for(String curS : outputs) {
      AbstractState curState = storeHelper.buildStateFromString(funName, curS, storeHelper.convertOthersToSSAMAP(others));
      returnStates.add(curState);
    }

    return new OneFileStore(funName, inputState, returnStates);
  }

  public AbstractState getInputState() {
    return inputState;
  }


  public void setInputState(AbstractState pInputState) {
    inputState = pInputState;
  }


  public Collection<AbstractState> getReturnStates() {
    return returnStates;
  }


  public void setReturnStates(Collection<AbstractState> pReturnStates) {
    returnStates = pReturnStates;
  }

}
