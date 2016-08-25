package edu.uw.ece.bordeaux.engine;

import java.io.IOException;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.WorkerEngine.WorkerCallback;
import edu.mit.csail.sdg.alloy4whole.SimpleReporter;
import edu.uw.ece.bordeaux.util.Utils;

public class HolaSimpleReporter extends SimpleReporter {
	     
	public HolaSimpleReporter() {
		super(Utils.EmptyCallBack, Utils.TMP_DIRECTORY, true);
	}
	
//	public HolaSimpleReporter(A4Reporter parent) {
//		super(parent);
//	}
}
