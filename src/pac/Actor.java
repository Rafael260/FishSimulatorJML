/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package pac;

import java.util.List;



/**
 *
 * @author rafael
 */
public interface Actor {
    
    /**
     * Realiza a ação de acordo com a natureza específica
     * @param actors Lista de atuantes na simulação
     */
    public void act(List<Actor> actors);
    public boolean isAlive();
    public int getLinha();
    public void setLinha(int pos_linha);
    public int getColuna();
    public void setColuna(int pos_coluna);
}
