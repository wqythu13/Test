package org.sosy_lab.cpachecker.cpa.bam.incremental.program;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map.Entry;

public class ProgramDiffer {

	public static HashSet<String> programDiffer(HashMap<String, FunctionInfo> oldFunctionInfos, HashMap<String, FunctionInfo> newFunctionInfos) {
		for (Entry<String, FunctionInfo> curEntry : newFunctionInfos.entrySet()) {
		  FunctionInfo curInfo = curEntry.getValue();
			FunctionInfo tmpOldInfo = oldFunctionInfos.get(curInfo.getName());
			if(tmpOldInfo == null) {
				curInfo.setChanged(true);
				continue;
			}
			if(!SimpleDiffer.functionBodyDiffer(tmpOldInfo, curInfo)) {
        curInfo.setChanged(true);
      }
		}

		HashSet<String> resultSet = new HashSet<>();

		FunctionNode mainNode = new FunctionNode(ProgramInfo.getInstance().getMainInfo());
		FCG.createFunctionCallGraphAndUpdateChanges(mainNode, newFunctionInfos);

		for (Entry<String, FunctionInfo> curEntry : newFunctionInfos.entrySet()) {
		  FunctionInfo curInfo = curEntry.getValue();
			if(!curInfo.isChanged()) {
				resultSet.add(curInfo.getName());
			}
		}
		return resultSet;
	}

}
