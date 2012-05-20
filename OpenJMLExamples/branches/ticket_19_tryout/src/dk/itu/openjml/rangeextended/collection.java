package dk.itu.openjml.rangeextended;

import java.text.DateFormat;
import java.text.ParseException;
import java.util.List; 
import java.util.Arrays;
import java.util.Set;
import java.util.HashSet;
import java.util.Date;

//import dk.itu.openjml.rangeextended.Range;

/**
 * 
 * Based up xxx
 * in this article he name the class with a lower case (normal approach capitalize)
 * we guess its related to a kind of pattern since its not a real class/interface 
 * more a wrapper class for simplified instantialization...
 * 
 */
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

	// Don't use <S extends Comparable<T>>
	public static <S extends Comparable<S>> Range<S> Range( S from, S to ){
		return new Range( from, to );
	}
	
	// FIXME: look into this one not working yet
	// enable test if going to look into it
	public static Date Date( String date ){
		try {
			return DateFormat.getDateInstance().parse( date );
		}
		catch (ParseException e) {
			throw new RuntimeException( e );
		}
	}
	
	
	
	
}
