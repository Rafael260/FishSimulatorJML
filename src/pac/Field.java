/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package pac;

//import java.util.Random;
import java.util.Collections;
//import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

public abstract class Field {
    
    protected /*@ nullable spec_public @*/ Location[][] campo;
    protected /*@ spec_public @*/ int tamanhoAltura;
    protected /*@ spec_public @*/ int tamanhoLargura;
    
    private static final /*@ spec_public @*/ int TAMANHO_MINIMO = 5;
    private static final /*@ spec_public @*/ int TAMANHO_PADRAO = 50;
    
    //@ public instance constraint tamanhoAltura == \old(tamanhoAltura);
    //@ public instance constraint tamanhoLargura == \old(tamanhoLargura);
    
    //@ ensures tamanhoAdequado(height,width) ==> (tamanhoAltura == height);
    //@ ensures tamanhoAdequado(height,width) ==> (tamanhoLargura == width);
    //@ensures !tamanhoAdequado(height,width) ==> (tamanhoAltura == TAMANHO_PADRAO);
    //@ensures !tamanhoAdequado(height,width) ==> (tamanhoLargura == TAMANHO_PADRAO);
    public Field(int height, int width){
        if (tamanhoAdequado(height,width)){
            campo = new Location[height][width];
            tamanhoAltura = height;
            tamanhoLargura = width;
        }
        else{
            campo = new Location[TAMANHO_PADRAO][TAMANHO_PADRAO];
            tamanhoAltura = TAMANHO_PADRAO;
            tamanhoLargura = TAMANHO_PADRAO;
        }
        for (int linha = 0; linha < tamanhoAltura; linha++){
            for (int coluna = 0; coluna < tamanhoLargura; coluna++){
                campo[linha][coluna] = new Location(linha,coluna,this);
                campo[linha][coluna].inicializarNumeroDeAlgas();
            }
        }
    }
    
    /*@ public initially (\forall int i,j; i >= 0 && j >= 0 && i < tamanhoAltura && j < tamanhoLargura;
    @					 campo[i][j].getAtor() == null);
    @*/
    abstract public void atualizarAlgas();
    
    //@ requires estaNoIntervalo(row,col);
    //@ assignable \nothing;
    //@ ensures \result == (Fish) campo[row][col].getAtor();
    public /*@ nullable pure @*/ Fish getFishAt(int row, int col)
    {
        Actor ator = campo[row][col].getAtor();
        Fish fish = (Fish) ator;
        return fish;
    }

    //@assignable \nothing;
    //@ensures \result == tamanhoAltura;
    public /*@ pure @*/ int getHeight() {
        return tamanhoAltura;
    }

    //@assignable \nothing;
    //@ensures \result == tamanhoLargura;
    public /*@ pure @*/ int getWidth() {
        return tamanhoLargura;
    }
    
    //@ assignable \nothing;
    //@ensures \result ==> (linha >= 0 && coluna >= 0 && linha < tamanhoAltura && coluna < tamanhoLargura);
    public /*@ pure @*/ boolean estaNoIntervalo(int linha, int coluna){
        return linha >= 0 && coluna >= 0 && linha < tamanhoAltura && coluna < tamanhoLargura;
    }
    
    //Metodo estatico nao tem anotacao, ate onde eu sei
    public static /*@ pure @*/ boolean tamanhoAdequado(int height, int width){
        return height >= TAMANHO_MINIMO && width >= TAMANHO_MINIMO;
    }
    
    public static /*@ pure @*/ boolean saoAdjacentes(Location location1, Location location2){
    	Double x1 = (double) location1.getLinha();
    	Double y1 = (double) location1.getColuna();
    	Double x2 = (double) location2.getLinha();
    	Double y2 = (double) location2.getColuna();
    	boolean xAdjacente = Math.abs(x2 - x1) <= 1;
    	boolean yAdjacente = Math.abs(y2 - y1) <= 1;
    	return xAdjacente && yAdjacente;
    }
    
    //@requires estaNoIntervalo(linha,coluna);
    //@assignable \nothing;
    //@ensures \result == campo[linha][coluna];
    public /*@ pure @*/ Location getLocation(int linha, int coluna){
        return campo[linha][coluna];
    }
    
    //@requires loc != null;
    //@requires estaNoIntervalo(loc.getLinha(),loc.getColuna());
    //@assignable \nothing;
    //ensures \result == getAtor(loc.getLinha(),loc.getColuna());
    public /*@ nullable pure @*/ Actor getAtor(Location loc){
        return campo[loc.getLinha()][loc.getColuna()].getAtor();
    }
    
    //@ requires location != null;
    //@ assignable \nothing;
    //@ ensures \result != null;
    //Garante que todos os locais no resultado sao de fato adjacentes
    //Como garantir que sao adjacentes? Verifica os valores absolutos das diferencas das posicoes x,y
    //Essas diferencas nao podem ser maiores que 1
    /*@ ensures (\forall int i; 0 <= i && i < \result.size(); 
     @  saoAdjacentes((Location)\result.get(i),location));
     @*/
    public /*@ pure @*/ List<Location> getAdjacentes(Location location){
        List<Location> locations = new LinkedList<Location>();
        
        int linha = location.getLinha();
        int coluna = location.getColuna();
       
        int prox_linha;
        int prox_coluna;
        Location locationSearched;    
        for (int varia_linha = -1; varia_linha <= 1; varia_linha++){
            prox_linha = linha + varia_linha;
            for (int varia_coluna = -1; varia_coluna <= 1; varia_coluna++){
                prox_coluna = coluna + varia_coluna;
                //Se os indices novos estao dentro do campo e sao diferentes do proprio local em questao    
                if (estaNoIntervalo(prox_linha,prox_coluna) && ((varia_linha != 0) || varia_coluna != 0)){
                	locationSearched = this.campo[prox_linha][prox_coluna];
                	locations.add(locationSearched);
                }
            }

        }   
        
        //Baguncar a ordem, para que a escolha de qual posicao ir ser aleatoria
        Collections.shuffle(locations);
        
        return locations;
    }
    
    //@requires pos_adjacentes != null;
    //@assignable \nothing;
    //@ensures (\forall int i; 0 <= i && i < pos_adjacentes.size(); (((Location)pos_adjacentes.get(i)).getAtor() == null) ==> \result.contains(pos_adjacentes.get(i)));
    //@ensures (\forall int i; 0 <= i && i < \result.size(); ((Location)\result.get(i)).getAtor() == null);
    public /*@ pure @*/ List<Location> getAdjacentesLivres(List<Location> pos_adjacentes){
        List<Location> livres = new LinkedList<Location>();        
        for (Location loc_atual: pos_adjacentes){
            if (getAtor(loc_atual) == null){
                livres.add(loc_atual);
            }
        }
    
        return livres;
    }
     
    //@requires free != null;
    //@assignable \nothing;
    //@ensures (free.size() > 0) ==> (\result == free.get(0));
    public /*@ nullable pure @*/ Location getAdjacenteLivre(List<Location> free){
        if (free.size() > 0){
            return free.get(0);
        }
        else{
            return null;
        }
    }
    
    
    //@requires loc != null;
    //@ensures campo[loc.getLinha()][loc.getColuna()].getAtor() == null;
    public void limparPosicao(Location loc){
        campo[loc.getLinha()][loc.getColuna()].setAtor(null);
    }
    
    //@requires ator != null;
    //@requires location != null;
    //@ensures campo[location.getLinha()][location.getColuna()].getAtor().equals(ator);
    public void colocarAtor(Actor ator, Location location){
        campo[location.getLinha()][location.getColuna()].setAtor(ator);
    }  
}
