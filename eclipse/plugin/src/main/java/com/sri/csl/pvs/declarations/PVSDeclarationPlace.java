package com.sri.csl.pvs.declarations;

public class PVSDeclarationPlace {
	public int x1, y1, x2, y2;
	
	public PVSDeclarationPlace(int x1, int y1, int x2, int y2) {
		this.x1 = x1;
		this.y1 = y1;
		this.x2 = x2;
		this.y2 = y2;		
	}

	public String toString() {
		return String.format("Place<%d, %d, %d, %d>", x1, y1, x2, y2);
	}
	
}
