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
    
	//@public model instance boolean isActive;
	//@public model instance int row;
	//@public model instance int col;
	//@public model instance int age;
	
    public void act(List<Actor> actors);
    
    //@ensures \result ==> isActive;
    public boolean isAlive();
    
    public /*@ pure @*/ int getLinha();
    public void setLinha(int pos_linha);
    public /*@ pure @*/ int getColuna();
    public void setColuna(int pos_coluna);
    public /*@ pure @*/ boolean equals(Actor ator);
    public /*@ pure @*/ int getAge();
    public /*@ pure @*/ int getEnergia();
    public /*@ pure @*/ Location getLocation();
}
