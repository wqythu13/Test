package org.sosy_lab.cpachecker.cpa.bam.incremental.program;

import java.util.HashMap;

public class FCG {

	public static void createFunctionCallGraphAndUpdateChanges(FunctionNode curNode, HashMap<String, FunctionInfo> nameInfoMap) {
		if(curNode == null || curNode.getFunctionInfo() == null) {
      return;
    }
		FunctionInfo curInfo = curNode.getFunctionInfo();
		updateFunctionChanged(curNode);

		for(String calledName : curInfo.getCalledFunctionName()) {
			FunctionInfo callInfo = nameInfoMap.get(calledName);
			FunctionNode callNode = new FunctionNode(callInfo);
			callNode.setParentNode(curNode);
			curNode.addChildNodes(callNode);
			createFunctionCallGraphAndUpdateChanges(callNode, nameInfoMap);
		}
	}

	private static void updateFunctionChanged(FunctionNode fNode)
	{
		if(fNode.getFunctionInfo() != null)
		{
			if(fNode.getFunctionInfo().isChanged())
			{
				FunctionNode curNode = fNode.getParentNode();
				while(curNode != null)
				{
					curNode.getFunctionInfo().setChanged(true);
					curNode = curNode.getParentNode();
				}
			}
		}
	}

}
