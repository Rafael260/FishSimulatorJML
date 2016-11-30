package pac;

import java.util.List;
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
    private static final double BREED_PROBABILITY = 0.15;
    private static final int MAX_BREED = 4;
    private static final int SARDINE_FOOD_VALUE = 5;
    
    public Tuna(Field campo, int linha, int coluna) {
        super(campo,linha,coluna);
        nivelFome = inicializaFome(MAX_FOOD);
    }

    /**
     * O atum vai verificar se tem sardinha próxima pra comer. Caso não tiver, move aleatoriamente
     * @param actors A lista de novos atores que serão adicionados futuramente na lista principal
     */
    @Override
    public void act(List<Actor> actors) {
        incrementAge(MAX_AGE);
        decrementaNivelFome();
        darCria(actors);
        Location location = new Location(pos_linha,pos_coluna);
        Location newLocation = encontrarComida(location);
        
        //Se não encontrou comida
        if (newLocation == null){
           newLocation = campo.posicaoAdjacenteLivre(pos_linha,pos_coluna);
        }
        
        //Se newLocation é null, achou posição pra se mover
        if (newLocation != null){
            mover(location,newLocation);
        }
        
    }
    /**
     * Procura sardinhas em posições adjacentes
     * @param location: localização atual do atum
     * @return Localização de alguma sardinha, caso tenha, ou null, caso contrário
     */    
    public Location encontrarComida(Location location){
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
     * Dá cria se o randômico numfilhos for maior que zero.
     * @param novosAtores: Lista de novos atores que serão adicionados na lista principal
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
