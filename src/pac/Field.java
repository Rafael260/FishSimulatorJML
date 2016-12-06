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
    
    //@ ensures tamanhoAdequado(height,width) ==> (tamanhoAltura == height);
    //@ ensures tamanhoAdequado(height,width) ==> (tamanhoLargura == width);
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
    //@ requires estaNoIntervalo(row,col);
    //@ ensures \result == (Fish) campo[row][col].getAtor();
    public /*@ nullable pure @*/ Fish getFishAt(int row, int col)
    {
        Actor ator = campo[row][col].getAtor();
        Fish fish = (Fish) ator;
        return fish;
    }

    public /*@ pure @*/ int getHeight() {
        return tamanhoAltura;
    }

    public /*@ pure @*/ int getWidth() {
        return tamanhoLargura;
    }
    
    //@ensures \result ==> (linha >= 0 && coluna >= 0 && linha < tamanhoAltura && coluna < tamanhoLargura);
    public /*@ pure @*/ boolean estaNoIntervalo(int linha, int coluna){
        return linha >= 0 && coluna >= 0 && linha < tamanhoAltura && coluna < tamanhoLargura;
    }
    //Metodo estatico nao tem anotacao, ate onde eu sei
    public static /*@ pure @*/ boolean tamanhoAdequado(int height, int width){
        return height >= TAMANHO_MINIMO && width >= TAMANHO_MINIMO;
    }
    
    public static /*@ pure @*/boolean saoAdjacentes(Location location1, Location location2){
    	Double x1 = (double) location1.getLinha();
    	Double y1 = (double) location1.getColuna();
    	Double x2 = (double) location2.getLinha();
    	Double y2 = (double) location2.getColuna();
    	Double resultado = Math.abs(y2 - y1) + Math.abs(x2 - x1);
    	return resultado > 0 && resultado < 3;
    }
    
    //@requires linha >= 0;
    //@requires coluna >= 0;
    //@ensures \result == campo[linha][coluna];
    public /*@ pure @*/ Location getLocation(int linha, int coluna){
        return campo[linha][coluna];
    }
    
    //@requires loc != null;
    //@ensures \result == getAtor(loc.getLinha(),loc.getColuna());
    public /*@ nullable pure @*/ Actor getAtor(Location loc){
        return getAtor(loc.getLinha(),loc.getColuna());
    }
    
    //Podemos tratar uma excecao aqui, com base na linha e coluna que esta acessando
    //@requires estaNoIntervalo(linha,coluna);
    //@ensures \result == campo[linha][coluna].getAtor();
    public /*@ nullable pure @*/ Actor getAtor (int linha, int coluna){
        return campo[linha][coluna].getAtor();
    }
   
    //@ requires location != null;
    //@ ensures \result != null;
    //Garante que todos os locais no resultado sao de fato adjacentes
    //Como garantir que sao adjacentes? Soma o valor absoluto das diferencas das posicoes x,y
    //abs(x2 - x1) + abs(y2 - y1)
    //Esse valor deve ser maior que zero (nao pode se tratar do mesmo local) e menor que tres (nao seria adjacente)
    /*@ ensures (\forall int i; 0 <= i && i < \result.size(); 
     @  saoAdjacentes((Location)\result.get(i),location));
     @*/
    public /*@ pure @*/ List<Location> adjacentes(Location location){
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
    
    public /*@ pure @*/ List<Location> getPosicoesAdjacentesLivres(Location location){
        List<Location> livres = new LinkedList<>();
        List<Location> pos_adjacentes = adjacentes(location);
        
        for (Location loc_atual: pos_adjacentes){
            if (getAtor(loc_atual) == null){
                livres.add(loc_atual);
            }
        }
    
        return livres;
    }
    
    public /*@ pure @*/ List<Location> getPosicoesAdjacentesLivres(int linha, int coluna){
        Location location = this.campo[linha][coluna];
    	return getPosicoesAdjacentesLivres(location);
    }
    
    public /*@ nullable @*/ Location posicaoAdjacenteLivre(Location location){
        List<Location> free = getPosicoesAdjacentesLivres(location);
        if (free.size() > 0){
            return free.get(0);
        }
        else{
            return null;
        }
    }
    
    public /*@ nullable pure @*/ Location posicaoAdjacenteLivre(int linha, int coluna){
        Location location = this.campo[linha][coluna];
    	return posicaoAdjacenteLivre(location);
    }
    
    //@ requires estaNoIntervalo(linha,coluna);
    //O ASSIGNABLE DA ERRO
    // assignable campo[linha][coluna].getAtor();
    //@ ensures campo[linha][coluna].getAtor() == null;
    public void limparPosicao(int linha, int coluna){
    	campo[linha][coluna].setAtor(null);
    }
    
    //O ASSIGNABLE DA ERRO
    //assignable campo[location.getLinha()][location.getColuna()].getAtor();
    //@requires loc != null;
    //@ensures campo[loc.getLinha()][loc.getColuna()].getAtor() == null;
    public void limparPosicao(Location loc){
        campo[loc.getLinha()][loc.getColuna()].setAtor(null);
    }
    
    //O ASSIGNABLE DA ERRO
    //assignable campo[location.getLinha()][location.getColuna()].getAtor();
    //@requires ator != null;
    //@requires location != null;
    //@ensures campo[location.getLinha()][location.getColuna()].getAtor().equals(ator);
    public void colocarAtor(Actor ator, Location location){
        campo[location.getLinha()][location.getColuna()].setAtor(ator);
    }
    
    //@requires estaNoIntervalo(linha,coluna);
    //@ensures campo[linha][coluna].getAtor().equals(ator);
    public void colocarAtor(Actor ator, int linha, int coluna){
        Location newLocation = this.campo[linha][coluna];
    	colocarAtor(ator,newLocation);
    }  
}
