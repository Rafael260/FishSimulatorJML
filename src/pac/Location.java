/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package pac;

import java.util.Random;

public class Location {
    private /*@ spec_public @*/int linha;
    private /*@ spec_public @*/ int coluna;
    private /*@ spec_public @*/ int numAlgas;
    private /*@ spec_public nullable @*/ Actor ator;
    
    private static final int MAX_ALGAS = 10;
    
    public Location(int l, int c){
        linha = l;
        coluna = c;
        numAlgas = 0;
        ator = null;
    }

    public /*@ pure @*/ int getLinha() {
        return linha;
    }

    public /*@ pure @*/ int getColuna() {
        return coluna;
    }

    public /*@ pure @*/ int getNumAlgas() {
        return numAlgas;
    }
    
    public /*@ nullable pure @*/ Actor getAtor() {
        return ator;
    }

    public void setAtor(/*@ nullable @*/ Actor ator) {
        this.ator = ator;
    }
        
    public void incrementaAlgas(){
        if (numAlgas < MAX_ALGAS){
           numAlgas++;
        }
    }
    
    public void decrementaAlgas(){
        if (numAlgas > 0){
            numAlgas--;
        }
    }

    public void definirNumeroDeAlgas(){
        Random random = new Random();
        numAlgas = random.nextInt(MAX_ALGAS+1);
    }
}
