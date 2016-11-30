package pac;

import java.util.Iterator;
import java.util.List;
import java.util.Random;


/**
 * A simple model of a shark.
 * Sharks age, move, breed, and die.
 * Sharks eat groper or herring but they prefer groper.
 * Sharks are loners - they prefer not to swim next to each other
 * @author Richard Jones and Michael Kolling
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
        super(campo,linha,coluna);
        nivelFome = inicializaFome(MAX_FOOD);
    }
    
    /**
     * O tubarão primeiramente procura comida. Se não encontrar, procura uma posição mais isolada.
     * Caso também consegue, vai para alguma aleatória, se tiver livre
     * @param actors 
     */
    @Override
    public void act(List<Actor> actors) {
        incrementAge(MAX_AGE);
        decrementaNivelFome();
        darCria(actors);
        Location location = new Location(pos_linha,pos_coluna);
        Location newLocation = encontrarComida(location);
        
        if (newLocation == null){
            //System.out.println("Nao axei comida, vou tentar me isolar");
            newLocation = isolar_se(campo.getPosicoesAdjacentesLivres(location));
        }
        
        if (newLocation == null){
            //System.out.println("Nao me isolei, vou pra onde der");
            newLocation = campo.posicaoAdjacenteLivre(pos_linha,pos_coluna);
        }
        
        if (newLocation != null){
            mover(location,newLocation);
        }
    }
    
    /**
     * Método responsável para achar comida nas posições adjacentes
     * @param location: Local atual do tubarão
     * @return A localização que ele deve ir caso consiga comida
     */
    public Location encontrarComida(Location location){
        //Pega a lista de locais adjacentes à ele
        List<Location> adjacents = campo.adjacentes(location);
        Iterator<Location> it = adjacents.iterator();
        //Procura se ao redor dele possui atum, pois é sua preferência
        Location newLocation = encontrarAtum(adjacents);
        if (newLocation != null)
            return newLocation;
        
        Actor ator;
        Sardine sardine;
        while (it.hasNext()){
            newLocation = it.next();
            ator = campo.getAtor(newLocation);
            //Mesma lógica para a sardinha
            if (ator instanceof Sardine){
                sardine = (Sardine) ator;
                if (sardine.isAlive()){
                    sardine.setMorto();
                    this.alimenta(SARDINE_FOOD_VALUE, MAX_FOOD);
                    return newLocation;
                }
            }
        
        }
        //Caso não encontrar nenhuma comida, retornará null
        return null;
    }
    
    public Location encontrarAtum(List<Location> adjacentes){
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
    
    /**
     * Procura locais adjacentes tais que as adjacentes destas não possua tubarão
     * @param adjacents: lista de adjacentes do tubarão atual
     * @return: Localização mais isolada, ou null caso não for possível
     */
    public Location isolar_se(List<Location> adjacents){
        Iterator<Location> it = adjacents.iterator();
        Location location;
        while (it.hasNext()){
            location = it.next();
            //Se essa posição adjacente não tiver tubarão próximo
            if (naoTemTubaraoProximo(location)){
                return location;
            }
        }
        
        return null;
    }
    
    /**
     * Verifica as posições adjacentes para ver se possui tubarão próximo
     * @param location: localização a ser testada
     * @return true caso estiver isolada, false, caso contrário
     */
    public boolean naoTemTubaraoProximo(Location location){
        List<Location> adjc = campo.adjacentes(location);
        Iterator <Location> it = adjc.iterator();
        Location aux;
        Actor ator;
        while (it.hasNext()){
            aux = it.next();
            ator = campo.getAtor(aux);
            //Se a posição adjacente possuir um tubarão que não seja o próprio que está testando
            if (ator instanceof Shark){
                if (ator != this) {
                    return false;
                }
            }
        }
        //Caso tiver passado por todas as localizações, e não achar nenhum tubarão, retorna true
        return true;
    }
    
    /**
     * Método para gerar novos tubarões
     * @param atores: Lista de novos tubarões, que futuramente serão adicionados na lista principal
     */
    public void darCria(List<Actor> atores){
        //Pega a lista de posições adjacentes livres para poder criar os filhos
        List<Location> livres = campo.getPosicoesAdjacentesLivres(pos_linha,pos_coluna);
        //recebe o número randômico de filhos que poderá ter
        int numFilhos = numeroDeFilhos(BREED_AGE,BREED_PROBABILITY,MAX_BREED);
        Location local_atual;
        //Adiciona os filhos nas posições adjacentes
        for (int i = 0; i < numFilhos && livres.size() > 0; i++){
            local_atual = livres.remove(0);
            Shark newShark = new Shark(campo,local_atual.getLinha(),local_atual.getColuna());
            atores.add(newShark);
        }
    }
    
}
