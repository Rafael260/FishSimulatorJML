/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package pac;

import java.util.Random;

/**
 *
 * @author rafael
 */
public class Location {
    private int linha;
    private int coluna;
    private int numAlgas;
    private Actor ator;
    
    private static final int MAX_ALGAS = 10;
    
    public Location(int l, int c){
        linha = l;
        coluna = c;
        numAlgas = 0;
        ator = null;
    }

    public int getLinha() {
        return linha;
    }

    public int getColuna() {
        return coluna;
    }

    public int getNumAlgas() {
        return numAlgas;
    }

    public Actor getAtor() {
        return ator;
    }

    public void setAtor(Actor ator) {
        this.ator = ator;
    }
        
    /**
     * Aumenta o número de algas, respeitando o limite
     */
    public void incrementaAlgas(){
        if (numAlgas < MAX_ALGAS){
           numAlgas++;
        }
    }
    
    /**
     * Diminui o número de algas. É usado pela sardinha, que come alga
     */
    public void decrementaAlgas(){
        if (numAlgas > 0){
            numAlgas--;
        }
    }
    
    /**
     * Método para inicializar o número de algas em determinada posição
     */
    public void numeroRandomicoDeAlgas(){
        Random random = new Random();
        numAlgas = random.nextInt(MAX_ALGAS+1);
    }
}
