package dk.itu.openjml.rangeextended;

import java.util.Iterator;


/**
 * 
 * 
 *
 * @param <T>
 */
//
public class Range<T extends Comparable<T>> implements Iterable<T>{
//public class Range<T extends Comparable> implements Iterable<T>{
	
	private T from = null;
	private T to = null;

	public Range( T start, T end ){
		this.from = start;
		this.to = end;
	}

	public boolean contains( T value ){
		return
			from.compareTo( value ) <= 0 &&
			to.compareTo( value ) >= 0;
	}

	@Override
	public Iterator<T> iterator() {

		Sequence<T> sequence = null;

		//String className = "dk.itu.openjml.rangeextended." + from.getClass().getSimpleName() + "Sequence";
		//dk.itu.openjml.rangeextended.IntegerSequence
		// but we have done some refactoring 
		String className = "dk.itu.openjml.rangeextended." + "Sequence" + from.getClass().getSimpleName();
		try {
			Class clazz = Class.forName( className );

			sequence = (Sequence<T>) clazz.getDeclaredConstructor( from.getClass() ).newInstance( from );

		}
		catch (Exception e) {
			throw new RuntimeException( "No Sequence found for type " + from.getClass() );
		}

		return new RangeIterator( sequence, to );
		
	}

}
