package dk.itu.openjml.range;

import java.util.Collection;


/**
 * 
 * http://www.unidata.ucar.edu/software/netcdf-java/v4.0/javadoc/ucar/ma2/Range.html
 * http://gleichmann.wordpress.com/2008/01/21/declarative-programming-a-range-type-for-java/
 * http://stackoverflow.com/questions/1314650/using-java-map-for-range-searches
 * 
 * 
 * This IRange does unfortunately no support *wholes* in the sequences...
 * - but think over an re implementation where  
 * 
 * Range - always have start - end and never wholes
 * Sequence - which can consist of multiple ranges
 * supporting wholes... - the hard part here is of course the to compute the 
 * sequence *out*.... 
 *
 * @param <T>
 */
public interface IRange<T> {
	
	
	// TODO: is it possible to set up some sort off constructor
	// had liked to add some jml specs in form of invariants here
	// something that must hold through he whole way...

	
	/**
	 * 
	 * @return
	 */
	//@ TODO: add some jml specs
	public T getFrom();
	
	/**
	 * 
	 * @return
	 */
	//@ TODO: add some jml specs
	public T getTo();
	
	
	
	
	// TODO: union - intersection is not a good idea 
	// on range e.g. for sequences / intervals with whols
	// Range(0, 100).union(Range(200, 300)) - think more in terms
	// of a hashmap with ranges ... ?
	
	/**
	 * Perform an union between two ranges
	 * and return a new range - FIXME: is this right
	 * 
	 * @param r
	 * @return
	 */
	//@ TODO: add some jml specs
	public Range union(Range r);

	
	/**
	 * Perform an intersection between two ranges
	 * and return a new range - FIXME: is this right
	 * 
	 * @param r
	 * @return
	 */
	//@ TODO: add some jml specs
	public Range intersection(Range r);
	
	/**
	 * Get a computed sequence in the shape of a collection
	 * - naive approach - FIXME: is this right
	 *   
	 * @return
	 */
	//@ TODO: add some jml specs
	public Collection<T> compute();

}
