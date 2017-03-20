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
package org.sosy_lab.cpachecker.util.predicates.interfaces;

import java.util.List;

import org.sosy_lab.cpachecker.exceptions.SolverException;
import org.sosy_lab.cpachecker.util.predicates.interfaces.view.QuantifiedFormulaManagerView;


/**
 * This interface represents the a theory with quantifiers.
 *
 *    ATTENTION: Not every theory has the quantifier elimination property!
 *
 *    ATTENTION: Please consider the additional functions in {@link QuantifiedFormulaManagerView}}!
 */
public interface QuantifiedFormulaManager {

  /**<
   * @return An existential quantified formula.
   *
   * @param pVariables  The variables that will get bound (variables) by the quantification.
   * @param pBody       The {@link BooleanFormula}} within that the binding will be performed.
   */
  public BooleanFormula exists (List<? extends Formula> pVariables, BooleanFormula pBody);

  /**
   * @return An universal quantified formula.
   *
   * @param pVariables  The variables that will get bound (variables) by the quantification.
   * @param pBody       The {@link BooleanFormula}} within that the binding will be performed.
   */
  public BooleanFormula forall (List<? extends Formula> pVariables, BooleanFormula pBody);

  /**
   * Eliminate the quantifiers for a given formula.
   *
   * @param   Formula with quantifiers.
   * @return  New formula without quantifiers.
   */
  public BooleanFormula eliminateQuantifiers(BooleanFormula pF) throws InterruptedException, SolverException;

}