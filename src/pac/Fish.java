package pac;

import java.util.Random;


/**
 * Write a description of class Fish here.
 * 
 * NOTE: This should serve as a superclass to all specific tyes of fish
 * 
 * @author (your name) 
 * @version (a version number or a date)
 */
public abstract class Fish implements Actor
{
    protected /*@ nullable @*/ Random random;
    protected boolean isAlive;
    protected int age;
    protected int nivelFome;
    protected int pos_linha;
    protected int pos_coluna;
    protected /*@ nullable @*/Field campo;
    
    /**
     * Constructor for objects of class Fish
     */
    public Fish(Field campo, int linha, int coluna)
    {
        random = new Random();
        isAlive = true;
        nivelFome = 15;
        age = 0;
        this.campo = campo;
        pos_linha = linha;
        pos_coluna = coluna;
        campo.colocarAtor(this, linha, coluna);
    }
    /**
     * Funcao para saber se o ator esta vivo
     */
    @Override
    public boolean isAlive() {
        return isAlive;
    }
    
    /**
     * 
     * @return a idade do ator
     */
    public int getAge() {
        return age;
    }

    public void setAge(int age) {
        this.age = age;
    }

    @Override
    public int getLinha() {
        return pos_linha;
    }

    @Override
    public void setLinha(int pos_linha) {
        this.pos_linha = pos_linha;
    }

    @Override
    public int getColuna() {
        return pos_coluna;
    }

    @Override
    public void setColuna(int pos_coluna) {
        this.pos_coluna = pos_coluna;
    }
    
    /**
     * Esvazia a posicao que o ator estava e marca como morto, para ser excluido da lista
     */        
    public void setMorto(){
        campo.limparPosicao(pos_linha, pos_coluna);
        isAlive = false;
    }
    
    /**
     * Inicia a fome de forma aleatoria
     */
    public  int inicializaFome(int maxFood){
        return random.nextInt(maxFood - 10) + 10;
    }
    
    /**
     * Aumenta em 1 unidade a idade, e o seta morto caso atinga a idade máxima
     * @param maxAge é a idade máxima
     */
    public void incrementAge(int maxAge){
        age++;
        if (age > maxAge)
            this.setMorto();
    }
    /**
     * Diminui 1 da fome, se zerar, seta morto
     */
    public void decrementaNivelFome(){
        nivelFome--;
        if (nivelFome <= 0){
            setMorto();
        }
    }
    
    /**
     * O ator chama esse metodo quando encontra comida, aumenta seu nivel da energia
     */
    public void alimenta(int valor, int maxFood){
        nivelFome += valor;
        if (nivelFome > maxFood){
            nivelFome = maxFood;
        }
        
    }
    
    /**
     * Move o ator de posicao no tabuleiro
     */
    public void mover(Location location, Location newLocation){
        campo.colocarAtor(this, newLocation);
        pos_linha = newLocation.getLinha();
        pos_coluna = newLocation.getColuna();
        campo.limparPosicao(location);
    }
    
    /**
     * Metodo usado para saber quando o ator pode ter filho
     */
    public boolean podeTerFilho(int idadeMinima){
        return age >= idadeMinima;
    }

    /**
     * Metodo responsavel para dizer quantos filhos um ator podera ter num determinado momento
     * e usado um randomico
     */
    public int numeroDeFilhos(int idadeMinima, double probabilidade, int maxFilhos){
        int numFilhos = 0;
        if (podeTerFilho(idadeMinima) && random.nextDouble() <= probabilidade){
            numFilhos = random.nextInt(maxFilhos) + 1;
        }
        return numFilhos;
    }
    
}
