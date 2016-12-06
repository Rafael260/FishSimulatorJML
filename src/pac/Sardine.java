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
        nivelEnergia = inicializaFome(MAX_FOOD);
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
        
        Location loc_atual = getLocation();
        
        //Primeiro procura andar agrupado
        Location newLocation = flocking(campo.getPosicoesAdjacentesLivres(loc_atual));
        
        if (loc_atual.getNumAlgas() > 0){
            alimenta(1,MAX_FOOD);
            loc_atual.decrementaAlgas();
        }
        //Coloca em newLocation a nova posicao aleatoria livre, caso nao consiga andar agrupado
        if (newLocation == null){
            newLocation = campo.posicaoAdjacenteLivre(pos_linha,pos_coluna);
        }
        //Poderia mudar para um try catch, tenta se movimentar
        //Se achou alguma posicao, se movimenta
        if (newLocation != null){
            mover(getLocation(),newLocation);
        }
    }
    
    /**
     * Usa o metodo numeroDeFilhos que gera randomicamente um numero, que se for maior que zero
     * e livres possuir ao menos uma posicao, cria novas sardinhas
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
     * Fazem as sardinhas procurarem posicoes que tem sardinhas proximas e que nao tem predadores
     * @param adjacentes Posicoes livres adjacentes
     * @return A localizacao, caso consiga uma, null caso contrario
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
            //Se a posicao adjacente possuir um predador
            if (ator instanceof Shark || ator instanceof Tuna){
                return false;   
            }
        }
        //Caso tiver passado por todas as localizacoes, e nao achar nenhum tubarao ou atum, retorna true
        return true;
    }

	
}
