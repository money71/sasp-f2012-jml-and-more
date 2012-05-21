package dk.itu.openjml.rangeextended;

public interface Sequence<T> {

	public T value();

	public Sequence<T> next();

	public Sequence<T> previous();
	
}
