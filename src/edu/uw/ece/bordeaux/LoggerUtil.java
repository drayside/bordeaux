package edu.uw.ece.bordeaux;

import java.io.FileNotFoundException;
import java.io.IOException;

import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4compiler.ast.Command;

public class LoggerUtil {

	

	public static int DEBUG_LEVEL = 1;
	

	public static synchronized void fileLogger(String reportFile, String... params){
		String out = "";
		try {
			out = edu.mit.csail.sdg.alloy4.Util.readAll(reportFile);
		} catch (FileNotFoundException e) {}
		catch (IOException e) {e.printStackTrace();}

		StringBuilder sb = new StringBuilder();
		sb.append(out);
		if(params.length > 0)
			sb.append("\n");
		for(String param:params){
			sb.append(param);
			sb.append(",");
		}
		if(params.length > 0)
			sb.deleteCharAt(sb.length()-1);
		try{
			edu.mit.csail.sdg.alloy4.Util.writeAll(reportFile, sb.toString());
		} catch (Err e) {
			e.printStackTrace();
		}

	}

	public static String hLine(final int n){
		StringBuilder result = new StringBuilder();
		for(int i = 0; i < n; i++){
			result.append('-');
		}
		result.append('\n');
		return result.toString();
	}
	
	public static void Detaileddebug( Object object,String format, Object...args){
		cosoleLogger(2,object.getClass(),format,args);
	}
	
	public static <T> void Detaileddebug( Class<T> clazz,String format, Object...args){
		cosoleLogger(2,clazz.getClass(),format,args);
	}
	
	public static <T> void Detaileddebug( String format, Object...args){
		cosoleLogger(2,LoggerUtil.class.getClass(),format,args);
	}
	
	public static void debug( Object object,String format, Object...args){
		cosoleLogger(1,object.getClass(),format,args);
	}
	
	public static <T> void debug( Class<T> clazz,String format, Object...args){
		cosoleLogger(1,clazz.getClass(),format,args);
	}
	
	public static <T> void debug( String format, Object...args){
		cosoleLogger(1,LoggerUtil.class.getClass(),format,args);
	}
	
	public static <T> void cosoleLogger(int level, Class<T> clazz,String format, Object...args){
		if(level < DEBUG_LEVEL)
			return;
		System.out.printf("%n[%s]: ", clazz.getName());
		System.out.printf(format, args);
		System.out.printf("%n");
	}


}
