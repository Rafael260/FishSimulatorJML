/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package pac;

import java.util.List;



/**
 *
 * @author rafael
 */
public interface Actor {
    
	/*@ public model instance boolean isActive;
	  @ initially isActive==true;
	  @*/
	
	//@public model instance int row;
	
	//@public model instance int col;
	
	/*@public model instance int ageOf;
	  @ initially ageOf==0;
	  @*/
	
    public void act(List<Actor> actors);
    
    //@ensures \result ==> isActive;
    public /*@ pure @*/ boolean isAlive();
    
    //@ensures \result == row;
    public /*@ pure @*/ int getLinha();
    
    //@assignable row;
    //@ensures row == pos_linha;
    public void setLinha(int pos_linha);
    //@ensures \result == col;
    public /*@ pure @*/ int getColuna();
    
    //@assignable col;
    public void setColuna(int pos_coluna);
    public /*@ pure @*/ boolean equals(Actor ator);
    public /*@ pure @*/ int getAge();
    public /*@ pure @*/ int getEnergia();
    public /*@ pure @*/ Location getLocation();
}
