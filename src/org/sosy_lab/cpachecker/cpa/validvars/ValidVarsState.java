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
package org.sosy_lab.cpachecker.cpa.validvars;

import java.io.Serializable;

import org.sosy_lab.cpachecker.core.interfaces.AbstractQueryableState;
import org.sosy_lab.cpachecker.core.interfaces.AbstractState;
import org.sosy_lab.cpachecker.core.interfaces.Graphable;
import org.sosy_lab.cpachecker.exceptions.InvalidQueryException;


public class ValidVarsState implements AbstractState, AbstractQueryableState, Graphable, Serializable {

  private static final long serialVersionUID = 9159663474411886276L;
  private final ValidVars validVariables;

  public ValidVarsState(ValidVars pValidVars) {
    validVariables = pValidVars;
  }

  public ValidVars getValidVariables() {
    return validVariables;
  }

  @Override
  public String getCPAName() {
    return "ValidVars";
  }

  @Override
  public boolean checkProperty(String pProperty) throws InvalidQueryException {
    return pProperty == null ? false : validVariables.containsVar(pProperty);
  }

  @Override
  public Object evaluateProperty(String pProperty) throws InvalidQueryException {
    return Boolean.valueOf(checkProperty(pProperty));
  }

  @Override
  public void modifyProperty(String pModification) throws InvalidQueryException {
    throw new InvalidQueryException("Cannot modify values of valid vars state (" + this.getClass().getCanonicalName()
        + ").");
  }

  @Override
  public String toDOTLabel() {
    return validVariables.toStringInDOTFormat();
  }

  @Override
  public boolean shouldBeHighlighted() {
    return false;
  }
}
