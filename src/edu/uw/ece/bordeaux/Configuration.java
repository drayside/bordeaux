package edu.uw.ece.bordeaux;

import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.util.Properties;

public class Configuration {

	final public static String properties_path = "resources/debugger.expriment.config";
	
	final public static String PACE = "PACE";
	final public static String ONE_FOUND = "oneFound";
	final public static String USING_KODKOD = "usingKodkod";
	final public static String USING_KK_ITR = "usingKKItr";
	final public static String SYMMETRY_OFF = "symmetryOff";
	final public static String USING_SYMMETRY = "usingSymmetry";
	final public static String REPORT_FILE_NAME = "reportFileName";
	final public static boolean IsInDeubbungMode = false; //Boolean.parseBoolean(System.getProperty("debug")); 
	
	private final java.util.Properties props;
	private static Configuration myself = null;
	
	private Configuration(String path){
		this.props = new Properties();
		
			InputStream input = null;
			try{
				input = new FileInputStream(path);
				props.load(input);
			}catch(IOException ex){
				//File not found and now the default are called
				setDefaultProps();
				
			}
	}
	
	private void setDefaultProps(){
		props.setProperty(PACE, String.valueOf(1));
		props.setProperty(ONE_FOUND, String.valueOf(false));
		props.setProperty(USING_KODKOD, String.valueOf(true));
		props.setProperty(USING_KK_ITR, String.valueOf(false));
		props.setProperty(SYMMETRY_OFF, String.valueOf(true));
		props.setProperty(USING_SYMMETRY, String.valueOf(false));
		props.setProperty(REPORT_FILE_NAME, "");		
	}
	
	public static String getProp(String key){
		myself = myself==null ? new Configuration(properties_path) : myself;
		return myself.props.getProperty(key);
	}
	
	public static void setProp(String key, String value){
		myself = myself==null ? new Configuration(properties_path) : myself;
		myself.props.setProperty(key,value);
	}
	
	
	
}
