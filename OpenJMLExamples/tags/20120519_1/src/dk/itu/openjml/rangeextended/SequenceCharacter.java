package dk.itu.openjml.rangeextended;

public class SequenceCharacter implements Sequence<Character>{

	Character value = null;

	public SequenceCharacter( Character value ){
		this.value = value;
	}

	public Character value(){
		return value;
	}
	
	// FIXME next / previous actually handle out of range stuff ?
	// ok it loops see for integers testIntergerSequenceBasicOutSideRange 
	// - guess it is the same for char... - is this a sane approach
	
	public Sequence<Character> next() {
		return new SequenceCharacter( (char) ( ( (int) value) + 1 ) );
	}
	
	public Sequence<Character> previous() {
		return new SequenceCharacter( (char) ( ( (int) value) - 1 ) );
	}

	
}