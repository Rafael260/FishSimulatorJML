package pac;

import java.util.List;

/**
 * (Fill in description and author info here)
 */
public class Ocean extends Field
{   
    /**
     * Represent an ocean of the given dimensions.
     * @param height The height of the ocean.
     * @param width The width of the ocean.
     */
    public Ocean(int height, int width)
    {
        super(height,width);  
    }
    
    /**
     * Return the fish at the given location, if any.
     * @param row The desired row.
     * @param col The desired column.
     * @return The fish at the given location, or null if there is none.
     */
    @Override
    public Fish getFishAt(int row, int col)
    {
        Actor ator = campo[row][col].getAtor();
        Fish fish = (Fish) ator;
        return fish;
    }
    
    /**
     * Responsável pelo comportamento das algas, podendo se espalhar.
     */
    @Override
    public void atualizaAlgas(){
        List<Location> adjacent;
        for (int linha = 0; linha < tamanhoAltura; linha++){
            for (int coluna = 0; coluna < tamanhoLargura; coluna++){
                //Se tiver ao menos quatro algas nessa posição - definir qual número mais adequado
                if(campo[linha][coluna].getNumAlgas() > 4){
                    //Pega as posições adjacentes
                    adjacent = adjacentes(campo[linha][coluna]);
                    
                    //E se espalha para essa posição aleatória
                    adjacent.get(0).incrementaAlgas();
                }
            }
        }
    }    

}
