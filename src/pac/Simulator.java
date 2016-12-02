package pac;
import java.awt.Color;
import static java.lang.Thread.sleep;
import java.util.Iterator;
import java.util.List;
import java.util.LinkedList;
import java.util.Random;

/**
 * (Fill in description and author info here)
 */

public class Simulator
{
    private /*@ nullable spec_public @*/ Field campo;
    private /*@ nullable spec_public @*/ SimulatorView simView;
    private /*@ nullable spec_public @*/ List<Actor> atores;
    
    private static final double PROBABILIDADE_CRIAR_SHARK = 0.02;
    private static final double PROBABILIDADE_CRIAR_SARDINE = 0.08;
    private static final double PROBABILIDADE_CRIAR_TUNA = 0.07;
    
    
    public Simulator(int height, int width)
    {
        atores = new LinkedList<Actor>();
        campo = new Ocean(height, width);
        simView = new SimulatorView(height, width);
        
        // define in which color fish should be shown
        simView.setColor(Tuna.class, Color.orange);
        simView.setColor(Shark.class, Color.blue);
        simView.setColor(Sardine.class, Color.green);
    }
    
    public void populate(){
        Random rand = new Random();
        for (int linha = 0; linha < campo.getHeight(); linha++){
            for (int coluna = 0; coluna < campo.getWidth(); coluna++){
                if (rand.nextDouble() <= PROBABILIDADE_CRIAR_SHARK){
                    Shark shark = new Shark(campo,linha,coluna);
                    atores.add(shark);
                }
                else if (rand.nextDouble() <= PROBABILIDADE_CRIAR_SARDINE){
                    Sardine sardine = new Sardine(campo,linha,coluna);
                    atores.add(sardine);
                }
                else if (rand.nextDouble() <= PROBABILIDADE_CRIAR_TUNA){
                    Tuna tuna = new Tuna(campo,linha,coluna);
                    atores.add(tuna);
                }
                campo.getLocation(linha,coluna).definirNumeroDeAlgas();
            }
        }
    }
    
    public void run()
    {  
        populate();
        int i = 0;
        while (true){
            simView.showStatus(i, campo);
            //As algas existentes podem se espalhar pelo oceano
            campo.atualizaAlgas();
            //remove os atores que foram setados como mortos
            removeMortos();            
            acao();
            if (!simView.isViable(campo))
                return;
            //processSleep(300);
         i++;   
        }
    }
    
    public void processSleep(int miliseg){
        try{
            sleep(miliseg);
        }
        catch(Exception e){
            System.out.println("Deu erro no sleep");
        }
    }
    
    //Itera sobre a lista de atores, verificando quem foi morto
    public void removeMortos(){
        Actor atorAux;
        Iterator<Actor> it = atores.iterator();
        while (it.hasNext()){
            atorAux = it.next();
            if (!atorAux.isAlive()){
                it.remove();
                campo.limparPosicao(atorAux.getLinha(), atorAux.getColuna());
            }
        }
    }
    /**
     * Percorre os atores que ficaram vivos chamando o método act de cada um
     */
    public void acao(){
        List<Actor> novosAtores = new LinkedList<Actor>();
        Iterator<Actor> it = atores.iterator();
        Actor ator;
        while (it.hasNext()){
            ator = it.next();
            ator.act(novosAtores);
        }
        atores.addAll(novosAtores);
    }
}
