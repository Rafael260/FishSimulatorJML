package pac;

import java.util.List;

/**
 * (Fill in description and author info here)
 */
public class Ocean extends Field
{   
    public Ocean(int height, int width)
    {
        super(height,width);  
    }
    
    @Override
    public /*@ nullable @*/ Fish getFishAt(int row, int col)
    {
        Actor ator = campo[row][col].getAtor();
        Fish fish = (Fish) ator;
        return fish;
    }
    
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
