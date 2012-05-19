package dk.itu.openjml.rangeextended;

public class SequenceInteger implements Sequence<Integer>{

	Integer value = null;

	public SequenceInteger( Integer value ){
		this.value = value;
	}

	public Integer value(){
		return value;
	}

	// FIXME next / previous actually handle out of range stuff ?
	// ok it loops see for integers testIntergerSequenceBasicOutSideRange 
	// - guess it is the same for char... - is this a sane approach
	
	public Sequence<Integer> next() {
		return new SequenceInteger( value + 1 );
	}

	public Sequence<Integer> previous() {
		return new SequenceInteger( value - 1 );
	}

}