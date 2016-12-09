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
    public void atualizarAlgas(){
        List<Location> adjacent;
        for (int linha = 0; linha < tamanhoAltura; linha++){
            for (int coluna = 0; coluna < tamanhoLargura; coluna++){
                //Se tiver ao menos quatro algas nessa posicao
                if(campo[linha][coluna].getNumAlgas() > 4){
                    //Pega as posicoes adjacentes
                    adjacent = getAdjacentes(campo[linha][coluna]);
                    
                    //E se espalha para essa posicao aleatoria
                    adjacent.get(0).incrementarAlgas();
                }
            }
        }
    }    

}
