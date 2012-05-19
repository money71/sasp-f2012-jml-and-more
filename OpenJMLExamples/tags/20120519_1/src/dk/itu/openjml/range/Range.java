package dk.itu.openjml.range;

import java.util.Collection;
import java.util.LinkedHashSet;
import java.util.Set;



/**
 * 
 *
 * @param <T>
 */
// TODO: look up the way to do it with Comparable
public class Range<T extends Comparable> implements IRange<T> {

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
	public Range union(Range r) {
		
		T newFrom;
		T newTo;
		
		//this.from > r.getFrom() ? newFrom = r.getFrom() : newFrom = this.from;
		
//		true ? newFrom = 1 : newTo = 3; 
		
		return null;
	}

	@Override
	public Range intersection(Range r) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public LinkedHashSet<T> compute() {
//		LinkedHashSet<T> c = new LinkedHashSet<T>();
		// quick fix not really genric approach since we use it
		// move to a function - can we use reflection to generalize it
		// something for int, chars etc...
		// probably also a drawback to use reference type Integer		
		LinkedHashSet<Integer> c = new LinkedHashSet<Integer>();
		int i = (Integer) from;
		int h = (Integer) to;
		while(i <= h) {
			c.add(i);
			i++;
		}
		
		return (LinkedHashSet<T>) c;
	}

	@Override
	public T getFrom() {
		// TODO Auto-generated method stub
		return from;
	}

	@Override
	public T getTo() {
		
		// TODO Auto-generated method stub
		return to;
	}
}