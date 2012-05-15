package dk.itu.openjml.rangeextended;

import java.util.List; 
import java.util.Arrays;
import java.util.Set;
import java.util.HashSet;

public class collection {

	public static <T> List<T> List(T...elems){
		return Arrays.asList( elems );
	}
	
	
	public static <T> T[] Array(T...elems){
		return elems;
	}

	public static <T> Set<T> Set(T...elems){
		return new HashSet<T>( List( elems ) );
	}
	
}
