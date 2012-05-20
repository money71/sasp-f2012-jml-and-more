package dk.itu.openjml.rangeextended;

import java.util.Iterator;

// org: public class RangeIterator implements Iterator<T>{
// raised generic types ...
public class RangeIterator<T extends Comparable<T>> implements Iterator<T>{
	
	private Sequence<T> sequence = null;
	private T end = null;

	public RangeIterator( Sequence<T> sequence, T end ){
		this.sequence = sequence;
		this.end = end;
	}
	
	@Override
	public boolean hasNext() {
		return sequence.value().compareTo( end ) <= 0;
	}

	@Override
	public T next() {
		 T value = sequence.value();
		sequence = sequence.next();
		return value;
	}

	@Override
	public void remove() {
		// TODO Auto-generated method stub
		// should we do anything raise exception etc...
	}

}