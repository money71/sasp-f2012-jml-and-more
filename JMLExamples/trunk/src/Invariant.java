/*
 * 
 * Based upon package org.jmlspecs.samples.jmlrefman;
 * and the JML 2 refman.
 * 
 */
public class Invariant {

	boolean[] b;
	//@ invariant b != null && b.length == 6;

	//@ assignable b; 
	Invariant() { 
		b = new boolean[6]; 
	}
	
    public static void main (String[] args){
    	Invariant x = new Invariant();
    }

}