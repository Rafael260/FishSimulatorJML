package pac;

import java.util.List;

import exceptions.MorteException;

import java.util.Iterator;


/**
 * A simple model of a tuna.
 * Tuna age, move, breed, and die.
 * They eat herring.
 * 
 * @author Richard Jones and Michael Kolling
 */
public class Tuna extends Fish
{
    private static final int MAX_AGE = 53;
    private static final int MAX_FOOD = 29;
    private static final int BREED_AGE = 15;
    private static final double BREED_PROBABILITY = 0.14;
    private static final int MAX_BREED = 4;
    private static final int SARDINE_FOOD_VALUE = 5;
    
    public Tuna(Field campo, int linha, int coluna) {
        super(campo,linha,coluna,MAX_AGE);
        nivelEnergia = inicializaFome(MAX_FOOD);
    }

    /**
     * O atum vai verificar se tem sardinha próxima pra comer. Caso nao tiver, move aleatoriamente
     * @param actors A lista de novos atores que serao adicionados futuramente na lista principal
     */
    @Override
    public void act(List<Actor> actors) {
        try{
        	incrementAge(MAX_AGE);
        	decrementaNivelFome();
        }catch(MorteException e){
        	setMorto();
        }
        darCria(actors);
        Location location = campo.getLocation(pos_linha, pos_coluna);
        Location newLocation = encontrarComida(location);
        
        //Se nao encontrou comida
        if (newLocation == null){
        	List<Location> adjacentes = campo.adjacentes(location);
        	List<Location> livres = campo.getPosicoesAdjacentesLivres(adjacentes);
           newLocation = campo.posicaoAdjacenteLivre(livres);
        }
        
        //Se newLocation eh null, achou posicao pra se mover
        if (newLocation != null){
            mover(newLocation);
        }
        
    }
    /**
     * Procura sardinhas em posicoes adjacentes
     * @param location: localizacao atual do atum
     * @return Localizacao de alguma sardinha, caso tenha, ou null, caso contrario
     */    
    public /*@ nullable pure @*/ Location encontrarComida(Location location){
        List<Location> adjacents = campo.adjacentes(location);
        Iterator<Location> it = adjacents.iterator();
        Location newLocation;
        Actor ator;
        Sardine sardine;
        while (it.hasNext()){
            newLocation = it.next();
            ator = campo.getAtor(newLocation);
            if (ator instanceof Sardine){
                sardine = (Sardine) ator;
                if (sardine.isAlive()){
                    sardine.setMorto();
                    this.alimenta(SARDINE_FOOD_VALUE, MAX_FOOD);
                    return newLocation;
                }
            }
        }
        
        return null;
    }
    
    /**
     * Da cria se o randomico numfilhos for maior que zero.
     * @param novosAtores: Lista de novos atores que serao adicionados na lista principal
     */
    public void darCria(List<Actor> novosAtores){
        List<Location> livres = campo.getPosicoesAdjacentesLivres(pos_linha,pos_coluna);
        int numFilhos = numeroDeFilhos(BREED_AGE,BREED_PROBABILITY,MAX_BREED);
        Location local_atual;
        for (int i = 0; i < numFilhos && livres.size() > 0; i++){
            local_atual = livres.remove(0);
            Tuna newTuna = new Tuna(campo,local_atual.getLinha(),local_atual.getColuna());
            novosAtores.add(newTuna);
        }
    }
}