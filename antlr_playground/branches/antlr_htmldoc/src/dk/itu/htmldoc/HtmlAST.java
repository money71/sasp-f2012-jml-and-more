package dk.itu.htmldoc;

import org.antlr.runtime.tree.*;
import org.antlr.runtime.Token;

public class HtmlAST extends CommonTree {
	public String text; 
	
	public HtmlAST(Token t) {
		super(t);
		text = (t != null? t.getText(): "[]");
	}

	public String toString() {
		return text + super.toString();
	}
}