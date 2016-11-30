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
    
    protected /*@ nullable @*/ Location[][] campo;
    protected int tamanhoAltura;
    protected int tamanhoLargura;
    
    private static final int TAMANHO_MINIMO = 5;
    private static final int TAMANHO_PADRAO = 50;
    
    
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
                campo[linha][coluna] = new Location(linha,coluna);
                campo[linha][coluna].definirNumeroDeAlgas();
            }
        }
    }
    
    abstract public void atualizaAlgas();
    abstract public /*@ nullable @*/ Fish getFishAt(int row, int col);

    public int getHeight() {
        return tamanhoAltura;
    }

    public int getWidth() {
        return tamanhoLargura;
    }
    
    public boolean estaNoIntervalo(int linha, int coluna){
        return linha >= 0 && coluna >= 0 && linha < tamanhoAltura && coluna < tamanhoLargura;
    }
    
    
    public static boolean tamanhoAdequado(int height, int width){
        return height >= TAMANHO_MINIMO && width >= TAMANHO_MINIMO;
    }
    
    public Location getLocation(int linha, int coluna){
        return campo[linha][coluna];
    }
    
    public /*@ nullable @*/ Actor getAtor(Location loc){
        return getAtor(loc.getLinha(),loc.getColuna());
    }
    
    public /*@ nullable @*/ Actor getAtor (int linha, int coluna){
        if (estaNoIntervalo(linha,coluna))
            return campo[linha][coluna].getAtor();
        else{
            return null;
        }
    }
   
    //-------------------------------------------------------------------------------
    public List<Location> adjacentes(Location location){
    
        if (location == null){
            return null;
        }
        List<Location> locations = new LinkedList<>();
        
        int linha = location.getLinha();
        int coluna = location.getColuna();
         
        int prox_linha;
        int prox_coluna;
            
        //Faz for encadeado, variando a linha e coluna drecrementando e incrementando 1
        for (int varia_linha = -1; varia_linha <= 1; varia_linha++){
            prox_linha = linha + varia_linha;
            if (prox_linha >= 0 && prox_linha < tamanhoAltura){
                for (int varia_coluna = -1; varia_coluna <= 1; varia_coluna++){
                    prox_coluna = coluna + varia_coluna;
                    
                    if (prox_coluna >= 0 && prox_coluna < tamanhoLargura && ((varia_linha != 0) || varia_coluna != 0)){
                        locations.add(new Location(prox_linha,prox_coluna));
                    }
                }
            }
        }    
        
        Collections.shuffle(locations);
        
        return locations;
    }
    public List<Location> adjacentes(int linha, int coluna){
        return adjacentes(new Location(linha,coluna));
    }
    
    //-------------------------------------------------------------------------------
    public List<Location> getPosicoesAdjacentesLivres(Location location){
        List<Location> livres = new LinkedList<>();
        List<Location> pos_adjacentes = adjacentes(location);
        
        for (Location loc_atual: pos_adjacentes){
            if (getAtor(loc_atual) == null){
                livres.add(loc_atual);
            }
        }
    
        return livres;
    }
    
    public List<Location> getPosicoesAdjacentesLivres(int linha, int coluna){
        return getPosicoesAdjacentesLivres(new Location(linha,coluna));
    }
    
    //-------------------------------------------------------------------------------
    public /*@ nullable @*/ Location posicaoAdjacenteLivre(Location location){
        List<Location> free = getPosicoesAdjacentesLivres(location);
        if (free.size() > 0){
            return free.get(0);
        }
        else{
            return null;
        }
    }
    
    public /*@ nullable @*/ Location posicaoAdjacenteLivre(int linha, int coluna){
        return posicaoAdjacenteLivre(new Location(linha,coluna));
    }
    //-------------------------------------------------------------------------------
    
    
    public void limparPosicao(int linha, int coluna){
        limparPosicao(new Location(linha,coluna));
    }
    
    public void limparPosicao(Location loc){
        campo[loc.getLinha()][loc.getColuna()].setAtor(null);
    }
    
    public void colocarAtor(Actor ator, Location location){
        campo[location.getLinha()][location.getColuna()].setAtor(ator);
    }
    
    public void colocarAtor(Actor ator, int linha, int coluna){
        colocarAtor(ator,new Location(linha,coluna));
    }
    
}
