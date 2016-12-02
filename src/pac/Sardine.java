package pac;

import java.util.Iterator;
import java.util.List;
import java.util.Random;


/**
 * A simple model of a sardine.
 * sardines age, move, breed, and die.
 * They eat plankton.
 * They exhibit flocking behaviour - they tend to seek company. 
 * If they spot a predator close by, they panic.
 * 
 */
public class Sardine extends Fish
{
    private static final int MAX_AGE = 50;
    private static final int MAX_FOOD = 24;
    private static final int BREED_AGE = 14;
    private static final double BREED_PROBABILITY = 0.1;
    private static final int MAX_BREED = 3;
    
    public Sardine(Field campo, int linha, int coluna){
        super(campo,linha,coluna);
        //Inicializa a fome randomicamente
        nivelFome = inicializaFome(MAX_FOOD);
    }

    /**
     * A sardinha simplesmente procura um local aleatório para se movimentar
     * @param novosAtores 
     */
    @Override
    public void act(List<Actor> novosAtores){
        incrementAge(MAX_AGE);
        decrementaNivelFome();
        darCria(novosAtores);
        
        Location loc_atual = campo.getLocation(pos_linha, pos_coluna);
        
        //Primeiro procura andar agrupado
        Location newLocation = flocking(campo.getPosicoesAdjacentesLivres(loc_atual));
        
        if (loc_atual.getNumAlgas() > 0){
            alimenta(1,MAX_FOOD);
            loc_atual.decrementaAlgas();
        }
        //Coloca em newLocation a nova posição aleatória livre, caso não consiga andar agrupado
        if (newLocation == null){
            newLocation = campo.posicaoAdjacenteLivre(pos_linha,pos_coluna);
        }
        //Se achou alguma posição, se movimenta
        if (newLocation != null){
            mover(new Location(pos_linha,pos_coluna),newLocation);
        }
    }
    
    /**
     * Usa o método numeroDeFilhos que gera randomicamente um número, que se for maior que zero
     * e livres possuir ao menos uma posição, cria novas sardinhas
     * @param novosAtores 
     */
    public void darCria(List<Actor> novosAtores){
        List<Location> livres = campo.getPosicoesAdjacentesLivres(pos_linha,pos_coluna);
        int numFilhos = numeroDeFilhos(BREED_AGE,BREED_PROBABILITY,MAX_BREED);
        Location local_atual;
        for (int i = 0; i < numFilhos && livres.size() > 0; i++){
            local_atual = livres.remove(0);
            Sardine newSardine = new Sardine(campo,local_atual.getLinha(),local_atual.getColuna());
            novosAtores.add(newSardine);
        }
    }
    
    /**
     * Fazem as sardinhas procurarem posições que tem sardinhas próximas e que não tem predadores
     * @param adjacentes Posições livres adjacentes
     * @return A localização, caso consiga uma, null caso contrário
     */
    public /*@ nullable pure @*/ Location flocking(List<Location> adjacentes){
        
        Location newLocation;
        Iterator<Location> it = adjacentes.iterator();
        while (it.hasNext()){
            newLocation = it.next();
            if (temSardinha(campo.adjacentes(newLocation)) && naoTemPredador(campo.adjacentes(newLocation))){
                return newLocation;
            }
        }
        return null;
    }
    
    /**
     * Verifica se a posicao tem sardinha proxima.
     */
    public /*@ pure @*/ boolean temSardinha(List<Location> adjacentes){
        Iterator <Location> it = adjacentes.iterator();
        Location newLocation;
        Actor ator;
        while (it.hasNext()){
            newLocation = it.next();
            ator = campo.getAtor(newLocation);
            //Se a posicao adjacente possuir uma sardinha que nao seja a propria que esta testando
            if (ator instanceof Sardine){
                if (ator != this) {
                    return true;
                }
            }
        }
        
        return false;
    }
    /**
     * Verifica se a posicao esta livre de predadores
     * @param adjacentes: Posicoes adjacentes da posicao que esta testando
     * @return true se esta livre, false se tem predador proximo
     */
    public /*@ pure @*/ boolean naoTemPredador(List<Location> adjacentes){
        Iterator <Location> it = adjacentes.iterator();
        Location newLocation;
        Actor ator;
        while (it.hasNext()){
            newLocation = it.next();
            ator = campo.getAtor(newLocation);
            //Se a posicao adjacente possuir um tubarao
            if (ator instanceof Shark || ator instanceof Tuna){
                return false;   
            }
        }
        //Caso tiver passado por todas as localizacoes, e nao achar nenhum tubarao ou atum, retorna true
        return true;
    }
}
