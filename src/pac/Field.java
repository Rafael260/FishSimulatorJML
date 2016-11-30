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
/**
 *
 * @author rafael
 */
public abstract class Field {
    
    protected Location[][] campo;
    protected int tamanhoAltura;
    protected int tamanhoLargura;
    
    private final int TAMANHO_MINIMO = 5;
    private final int TAMANHO_PADRAO = 50;
    
    
    public Field(int height, int width){
        //Verifica se os parâmetros estão de acordo com o limite de tamanho mínimo
        if (tamanhoAdequado(height,width)){
            campo = new Location[height][width];
            tamanhoAltura = height;
            tamanhoLargura = width;
            
            
        }
        else{
            //caso não estiver, o tamanho padrão será usado
            campo = new Location[TAMANHO_PADRAO][TAMANHO_PADRAO];
            tamanhoAltura = TAMANHO_PADRAO;
            tamanhoLargura = TAMANHO_PADRAO;
        }
        //Percorrer toda a matriz inicializando cada posição
        for (int linha = 0; linha < tamanhoAltura; linha++){
            for (int coluna = 0; coluna < tamanhoLargura; coluna++){
                campo[linha][coluna] = new Location(linha,coluna);
                campo[linha][coluna].numeroRandomicoDeAlgas();
            }
        }
    }
    
    /**
     * A superclasse precisa ter a declaração do método
     */
    abstract public void atualizaAlgas();
    abstract public Fish getFishAt(int row, int col);

    /**
     * Altura do tabuleiro
     * @return: A altura da matriz 
     */
    public int getHeight() {
        return tamanhoAltura;
    }

    /**
     * Largura do tabuleiro
     * @return: A largura da matriz
     */
    public int getWidth() {
        return tamanhoLargura;
    }
    
    /**
     * Função para verificar se a posição (linha,coluna) está dentro do tabuleiro
     * @param linha Linha da posição
     * @param coluna Coluna da posição
     * @return Verdadeiro se tiver no tabuleiro, false caso contrário
     */
    public boolean estaNoIntervalo(int linha, int coluna){
        return linha >= 0 && coluna >= 0 && linha < tamanhoAltura && coluna < tamanhoLargura;
    }
    
    
   /**
    * Verifica se o campo está sendo construído com o tamanho mínimo adequado
    * @param height - altura
    * @param width - largura
    * @return 
    */ 
    public boolean tamanhoAdequado(int height, int width){
        return height >= TAMANHO_MINIMO && width >= TAMANHO_MINIMO;
    }
    
    /**
     * Pega a localização na posição (linha,coluna)
     * @param linha linha do tabuleiro
     * @param coluna coluna do tabuleiro
     * @return A localização desejada
     */
    public Location getLocation(int linha, int coluna){
        return campo[linha][coluna];
    }
    
    /**
     * Pega o ator que está na posição loc
     * @param loc localização no tabuleiro
     * @return o ator que está na posição
     */
    public Actor getAtor(Location loc){
        return getAtor(loc.getLinha(),loc.getColuna());
    }
    
    /**
     * Testa se a localização é válida e retorna o ator nessa posição
     * @param linha
     * @param coluna
     * @return o ator na posição (linha,coluna)
     */
    public Actor getAtor (int linha, int coluna){
        if (estaNoIntervalo(linha,coluna))
            return campo[linha][coluna].getAtor();
        else{
            return null;
        }
    }
   
    //-------------------------------------------------------------------------------
    /**
     * Procura as posições adjacentes ao redor da localização
     * @param location local para verificar suas adjacentes
     * @return: lista de Location adjacentes
     */
    public List<Location> adjacentes(Location location){
    
        if (location == null){
            return null;
        }
        //Cria uma lista de localizações adjacentes vazia
        List<Location> locations = new LinkedList<>();
        
        //Pega a posição da localização atual
        int linha = location.getLinha();
        int coluna = location.getColuna();
         
        //Variáveis para receber as localizações adjacentes
        int prox_linha;
        int prox_coluna;
            
        //Faz for encadeado, variando a linha e coluna drecrementando e incrementando 1
        for (int varia_linha = -1; varia_linha <= 1; varia_linha++){
            prox_linha = linha + varia_linha;
            if (prox_linha >= 0 && prox_linha < tamanhoAltura){
                for (int varia_coluna = -1; varia_coluna <= 1; varia_coluna++){
                    prox_coluna = coluna + varia_coluna;
                    
                    //Se a posição nova está dentro da matriz, ele adiciona como adjacente na lista
                    if (prox_coluna >= 0 && prox_coluna < tamanhoLargura && ((varia_linha != 0) || varia_coluna != 0)){
                        locations.add(new Location(prox_linha,prox_coluna));
                    }
                }
            }
        }    
        
        //Embaralha a ordem das posições, para que seja completamente aleatória a sequencia
        Collections.shuffle(locations);
        
        return locations;
    }
    /**
     * Chama o método adjacentes que contém Location como parâmetro
     * @param linha
     * @param coluna
     * @return 
     */
    public List<Location> adjacentes(int linha, int coluna){
        return adjacentes(new Location(linha,coluna));
    }
    
    //-------------------------------------------------------------------------------
    /**
     * Chama o método adjacentes, e coloca as posições livres em outra lista
     * @param location localização a ser testada
     * @return Lista de adjacentes que não tem nenhum ator
     */
    public List<Location> getPosicoesAdjacentesLivres(Location location){
        List<Location> livres = new LinkedList<>();
        List<Location> pos_adjacentes = adjacentes(location);
        
        for (Location loc_atual: pos_adjacentes){
            //Se essa posição tiver null, será adicionada na lsita de livres
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
    /**
     * Método para pegar uma posição livre adjacente, serve para realizar um movimento aleatório
     * @param location: localização atual do ator
     * @return: uma localização adjacente aleatória (pois a lista é embaralhada)
     */
    public Location posicaoAdjacenteLivre(Location location){
        List<Location> free = getPosicoesAdjacentesLivres(location);
        if (free.size() > 0){
            return free.get(0);
        }
        else{
            return null;
        }
    }
    
    public Location posicaoAdjacenteLivre(int linha, int coluna){
        return posicaoAdjacenteLivre(new Location(linha,coluna));
    }
    //-------------------------------------------------------------------------------
    
    
    public void limparPosicao(int linha, int coluna){
        limparPosicao(new Location(linha,coluna));
    }
    
    /**
     * Esvaziar posição
     * @param loc 
     */
    public void limparPosicao(Location loc){
        campo[loc.getLinha()][loc.getColuna()].setAtor(null);
    }
    
    /**
     * Colocar ator na determinada posição
     * @param ator
     * @param location 
     */
    public void colocarAtor(Actor ator, Location location){
        campo[location.getLinha()][location.getColuna()].setAtor(ator);
    }
    
    /**
     * Colocar ator na determinada posição
     * @param ator
     * @param linha
     * @param coluna 
     */
    public void colocarAtor(Actor ator, int linha, int coluna){
        colocarAtor(ator,new Location(linha,coluna));
    }
    
}
