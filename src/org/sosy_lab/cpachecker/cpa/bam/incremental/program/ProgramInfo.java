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
package org.sosy_lab.cpachecker.cpa.bam.incremental.program;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map.Entry;
import java.util.Set;

import org.sosy_lab.common.time.Timer;

public class ProgramInfo {
  private static ProgramInfo instance;

  private HashMap<String, FunctionInfo> oldFunctionInfo = new HashMap<>();
  private HashMap<String, FunctionInfo> nowFunctionInfo = new HashMap<>();
  private HashSet<String> unchangedFunSet = new HashSet<>();
  private FunctionInfo mainInfo = null;
  private HashMap<String, HashSet<String>> relativedFunMap = new HashMap<>();
  private HashMap<String, Integer> funcLineMap = new HashMap<>();
  private int unchangedFunSize = 0;
  private Timer readProgramInfoTimer = new Timer();
  private Timer writeProgramInfoTimer = new Timer();
  private Timer differProgramInfoTimer = new Timer();

  private ProgramInfo() {

  }

  public static ProgramInfo getInstance() {
    if(instance == null) {
      instance = new ProgramInfo();
    }
    return instance;
  }

  public void initProgramDiff() {
    differProgramInfoTimer.start();
    unchangedFunSet = ProgramDiffer.programDiffer(oldFunctionInfo, nowFunctionInfo);
    unchangedFunSize = unchangedFunSet.size();
    differProgramInfoTimer.stop();
  }

  public Set<String> getRelativeFunMap(String name) {
    if(relativedFunMap.size() == 0) {
      initRelativeFunMap();
    }
    return relativedFunMap.get(name);
  }

  private void initRelativeFunMap() {
    if(relativedFunMap.size() == 0) {
      for(Entry<String, FunctionInfo> curEntry : nowFunctionInfo.entrySet()) {
        String tmpName = curEntry.getKey();
        HashSet<String> calledFun = new HashSet<>(curEntry.getValue().getCalledFunctionName());
        calledFun.add(tmpName);
        relativedFunMap.put(tmpName, calledFun);
      }
    }
  }

  public HashMap<String, FunctionInfo> getOldFunctionInfo() {
    return oldFunctionInfo;
  }

  public void setOldFunctionInfo(HashMap<String, FunctionInfo> pOldFunctionInfo) {
    oldFunctionInfo = pOldFunctionInfo;
  }

  public HashMap<String, FunctionInfo> getNowFunctionInfo() {
    return nowFunctionInfo;
  }

  public void setNowFunctionInfo(HashMap<String, FunctionInfo> pNowFunctionInfo) {
    nowFunctionInfo = pNowFunctionInfo;
  }

  public HashSet<String> getUnchangedFunSet() {
    return unchangedFunSet;
  }

  public void setUnchangedFunSet(HashSet<String> pUnchangedFunSet) {
    unchangedFunSet = pUnchangedFunSet;
  }

  public int getUnchangedFunSize() {
    return unchangedFunSize;
  }

  public void setUnchangedFunSize(int pUnchangedFunSize) {
    unchangedFunSize = pUnchangedFunSize;
  }

  public FunctionInfo getMainInfo() {
    return mainInfo;
  }

  public void setMainInfo(FunctionInfo pMainInfo) {
    mainInfo = pMainInfo;
  }

  public void addFuncLineMap(String name, int num) {
    funcLineMap.put(name, num);
  }

  public int getFuncLineMap(String name) {
    if(!funcLineMap.containsKey(name)) {
      return -1;
    }
    return funcLineMap.get(name);
  }

  public void saveFunctionInfo(String filePath) {
    writeProgramInfoTimer.start();
    File pathFile = new File(filePath);
    if(!pathFile.exists()) {
      pathFile.mkdirs();
    }
    File file = new File(filePath + "/functionInfo.txt");
    ObjectOutputStream objectOutputStream = null;
    try {
      objectOutputStream = new ObjectOutputStream(new FileOutputStream(file));
      objectOutputStream.writeObject(nowFunctionInfo);
      objectOutputStream.close();
    } catch (FileNotFoundException e) {
      e.printStackTrace();
    } catch (IOException e) {
      if(objectOutputStream != null) {
        try {
          objectOutputStream.close();
        } catch (IOException e1) {
          e1.printStackTrace();
        }
      }
      e.printStackTrace();
    }
    writeProgramInfoTimer.stop();
  }

  public void readOldFunctionInfo(String filePath) {
    readProgramInfoTimer.start();
    if(filePath == null) {
      return;
    }
    File file = new File(filePath + "/functionInfo.txt");
    if(!file.exists()) {
      return;
    }
    HashMap<String, FunctionInfo> fInfos = null;
    ObjectInputStream objectInputStream = null;
    try {
      objectInputStream = new ObjectInputStream(new FileInputStream(file));
      fInfos = (HashMap<String, FunctionInfo>) objectInputStream.readObject();
    } catch (FileNotFoundException e) {
      e.printStackTrace();
    } catch (IOException e) {
      e.printStackTrace();
    } catch (ClassNotFoundException e) {
      e.printStackTrace();
    }
    finally {
      try {
        objectInputStream.close();
      } catch (IOException e) {
        e.printStackTrace();
      }
    }
    oldFunctionInfo = fInfos;
    readProgramInfoTimer.stop();
  }

  public Timer getReadProgramInfoTimer() {
    return readProgramInfoTimer;
  }

  public Timer getWriteProgramInfoTimer() {
    return writeProgramInfoTimer;
  }

  public Timer getDifferProgramInfoTimer() {
    return differProgramInfoTimer;
  }

}
