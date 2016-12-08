package pac;

import java.util.Iterator;
import java.util.List;
import java.util.Random;

import exceptions.MorteException;


/**
 * A simple model of a shark.
 * Sharks age, move, breed, and die.
 * Sharks eat groper or herring but they prefer groper.
 * Sharks are loners - they prefer not to swim next to each other
 */
public class Shark extends Fish
{
    
    private static final int MAX_AGE = 60;
    private static final int MAX_FOOD = 40;
    private static final int BREED_AGE = 18;
    private static final double BREED_PROBABILITY = 0.03;
    private static final int MAX_BREED = 3;
    private static final int SARDINE_FOOD_VALUE = 3;
    private static final int TUNA_FOOD_VALUE = 5;
    
    public Shark(Field campo, int linha, int coluna) {
        super(campo,linha,coluna,MAX_AGE);
        inicializarFome(MAX_FOOD);
    }
    
    /**
     * O tubarao primeiramente procura comida. Se nao encontrar, procura uma posicao mais isolada.
     * Caso tambem nao consegue, vai para alguma aleatoria, se tiver livre
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
        List<Location> adjacentes = campo.getAdjacentes(location);
        List<Location> livres = campo.getAdjacentesLivres(adjacentes);
        if (newLocation == null){
        	
            //System.out.println("Nao axei comida, vou tentar me isolar");
            newLocation = isolarSe(livres);
        }
        
        if (newLocation == null){
            //System.out.println("Nao me isolei, vou pra onde der");
            newLocation = campo.getAdjacenteLivre(livres);
        }
        
        //Se consegui achar um local para me mover, simbora
        if (newLocation != null){
            mover(newLocation);
        }
    }
    
    /**
     * Achar comida nas posicoes adjacentes
     */
    public /*@ nullable @*/ Location encontrarComida(Location location){
        //Pega a lista de locais adjacentes a  ele
        List<Location> adjacents = campo.getAdjacentes(location);
        //Procura se ao redor dele possui atum, pois eh sua preferencia
        Location newLocation = encontrarAtum(adjacents);
        //Se achou algum atum
        if (newLocation != null){
        	return newLocation;
        }
        newLocation = encontrarSardinha(adjacents);
        //Se achou alguma sardinha
        if (newLocation != null){
        	return newLocation;
        }
        //Caso nao encontrar nenhuma comida, retorna null
        return null;
    }
    
    public /*@ nullable @*/ Location encontrarAtum(List<Location> adjacentes){
        Iterator<Location> it = adjacentes.iterator();
        Location newLocation;
        Tuna tuna;
        while (it.hasNext()){
            newLocation = it.next();
            if (campo.getAtor(newLocation) instanceof Tuna){
                tuna = (Tuna) campo.getAtor(newLocation);
                if (tuna.isAlive()){
                    tuna.setMorto();
                    this.alimenta(TUNA_FOOD_VALUE, MAX_FOOD);
                }
                return newLocation;
            }
        }
        
        return null;
    }
    
    public /*@ nullable @*/ Location encontrarSardinha(List<Location> adjacentes){
    	Iterator<Location> it = adjacentes.iterator();
    	Location newLocation;
    	Actor ator;
        Sardine sardine;
        while (it.hasNext()){
            newLocation = it.next();
            ator = campo.getAtor(newLocation);
            //Mesma logica para a sardinha
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
     * Procura locais adjacentes tais que as adjacentes destas nao possua tubarao
     */
    public /*@ nullable @*/ Location isolarSe(List<Location> adjacents){
        Iterator<Location> it = adjacents.iterator();
        Location location;
        while (it.hasNext()){
            location = it.next();
            if (naoTemTubaraoProximo(location)){
                return location;
            }
        }
        
        return null;
    }
    
    /**
     * Verifica as posicoes adjacentes para ver se possui tubarao proximo
     */
    public /*@ pure @*/ boolean naoTemTubaraoProximo(Location location){
        List<Location> adjc = campo.getAdjacentes(location);
        Iterator <Location> it = adjc.iterator();
        Location aux;
        Actor ator;
        while (it.hasNext()){
            aux = it.next();
            ator = campo.getAtor(aux);
            if (ator instanceof Shark && ator != this){
                return false;
            }
        }
        return true;
    }
    
    /**
     * Metodo para gerar novos tubaroes
     */
    public void darCria(List<Actor> atores){
    	List<Location> adjacentes = campo.getAdjacentes(getLocation());
        List<Location> livres = campo.getAdjacentesLivres(adjacentes);
        int numFilhos = numeroDeFilhos(BREED_AGE,BREED_PROBABILITY,MAX_BREED);
        Location local_atual;
        //Adiciona os filhos nas posicoes adjacentes
        for (int i = 0; i < numFilhos && livres.size() > 0; i++){
            local_atual = livres.remove(0);
            Shark newShark = new Shark(campo,local_atual.getLinha(),local_atual.getColuna());
            atores.add(newShark);
        }
    }
  
}
