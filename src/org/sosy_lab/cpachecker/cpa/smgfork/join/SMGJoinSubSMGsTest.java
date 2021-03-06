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
package org.sosy_lab.cpachecker.cpa.smgfork.join;

import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;
import org.sosy_lab.cpachecker.cfa.types.MachineModel;
import org.sosy_lab.cpachecker.cpa.smgfork.SMGInconsistentException;
import org.sosy_lab.cpachecker.cpa.smgfork.graphs.SMGFactory;
import org.sosy_lab.cpachecker.cpa.smgfork.graphs.WritableSMG;
import org.sosy_lab.cpachecker.cpa.smgfork.objects.SMGObject;
import org.sosy_lab.cpachecker.cpa.smgfork.objects.SMGRegion;

public class SMGJoinSubSMGsTest {

  SMGJoinSubSMGs jssDefined;

  @Before
  public void setUp() throws SMGInconsistentException {
    WritableSMG smg1 = SMGFactory.createWritableSMG(MachineModel.LINUX64);
    WritableSMG smg2 = SMGFactory.createWritableSMG(MachineModel.LINUX64);
    WritableSMG destSmg = SMGFactory.createWritableSMG(MachineModel.LINUX64);

    SMGObject obj1 = new SMGRegion(8, "Test object 1");
    SMGObject obj2 = new SMGRegion(8, "Test object 2");

    smg1.addObject(obj1);
    smg2.addObject(obj2);

    SMGNodeMapping mapping1 = new SMGNodeMapping();
    SMGNodeMapping mapping2 = new SMGNodeMapping();

    jssDefined = new SMGJoinSubSMGs(SMGJoinStatus.EQUAL, smg1, smg2, destSmg, mapping1, mapping2, obj1, obj2, null);
  }

  @Test
  public void testIsDefined() {
    Assert.assertTrue(jssDefined.isDefined());
  }

  @Test
  public void testGetStatusOnDefined() {
    Assert.assertNotNull(jssDefined.getStatus());
  }

  @Test
  public void testGetSMG1() {
    Assert.assertNotNull(jssDefined.getSMG1());
  }

  @Test
  public void testGetSMG2() {
    Assert.assertNotNull(jssDefined.getSMG2());
  }

  @Test
  public void testGetDestSMG() {
    Assert.assertNotNull(jssDefined.getDestSMG());
  }

  @Test
  public void testGetMapping1() {
    Assert.assertNotNull(jssDefined.getMapping1());
  }

  @Test
  public void testGetMapping2() {
    Assert.assertNotNull(jssDefined.getMapping2());
  }
}
