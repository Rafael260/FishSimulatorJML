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
    private /*@ spec_public @*/ Field campo;
    
    private static final /*@ spec_public @*/ int  MAX_ALGAS = 10;
    
    public Location(int linha, int coluna, Field campo){
        this.linha = linha;
        this.coluna = coluna;
        this.numAlgas = 0;
        this.ator = null;
        this.campo = campo;
    }
    //@ public initially numAlgas == 0 && ator == null;
    
    //@public invariant campo.estaNoIntervalo(this.linha,this.coluna);
    
    //@assignable \nothing;
    //@ensures \result == this.linha;
    public /*@ pure @*/ int getLinha() {
        return linha;
    }

    //@assignable \nothing;
    //@ensures \result == this.coluna;
    public /*@ pure @*/ int getColuna() {
        return coluna;
    }

    //@assignable \nothing;
    //@ensures \result == this.numAlgas;
    public /*@ pure @*/ int getNumAlgas() {
        return numAlgas;
    }
    
    //@assignable \nothing;
    //@ensures \result == this.ator;
    public /*@ nullable pure @*/ Actor getAtor() {
        return ator;
    }

    //@assignable this.ator;
    //@ensures this.ator == ator;
    public void setAtor(/*@ nullable @*/ Actor ator) {
        this.ator = ator;
    }
    
    //@assignable numAlgas;
    //@ensures (this.numAlgas < MAX_ALGAS) ==> (this.numAlgas == \old(this.numAlgas) + 1);
    //@ensures this.numAlgas <= MAX_ALGAS;
    public void incrementarAlgas(){
        if (numAlgas < MAX_ALGAS){
           numAlgas++;
        }
    }
    
    //@assignable numAlgas;
    //@ensures (numAlgas > 0) ==> (numAlgas == \old(numAlgas) - 1);
    //@ensures numAlgas >= 0;
    public void decrementarAlgas(){
        if (numAlgas > 0){
            numAlgas--;
        }
    }

    //@assignable numAlgas;
    //@ensures numAlgas <= MAX_ALGAS;
    //@ensures numAlgas >= 0;
    public void inicializarNumeroDeAlgas(){
        Random random = new Random();
        numAlgas = random.nextInt(MAX_ALGAS+1);
    }
    
    //@ assignable \nothing;
    //@ ensures \result ==> (this.linha == location.getLinha() && this.coluna == location.getColuna() && this.ator.equals(location.getAtor()));
    public /*@ pure @*/ boolean equals(Location location){
    	return this.linha == location.getLinha() && this.coluna == location.getColuna() && this.ator.equals(location.getAtor());
    }
}
