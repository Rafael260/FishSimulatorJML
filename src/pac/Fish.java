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
    protected /*@ spec_public @*/ boolean isAlive; // in isActive;
    protected /*@ spec_public @*/ int age;
    protected /*@ spec_public @*/ int nivelFome;
    protected /*@ spec_public @*/ int pos_linha;
    protected /*@ spec_public @*/ int pos_coluna;
    protected /*@ spec_public @*/ Field campo;
    
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
    
    /* protected represents
      @ isActive = (this.isAlive ? true : false);
       */
    /**
     * Funcao para saber se o ator esta vivo
     */
    @Override
    public /*@ pure @*/ boolean isAlive() {
        return this.isAlive;
    }
    
    /**
     * 
     * @return a idade do ator
     */
    public /*@ pure @*/ int getAge() {
        return age;
    }

    public void setAge(int age) {
        this.age = age;
    }

    @Override
    public /*@ pure @*/ int getLinha() {
        return pos_linha;
    }

    @Override
    public void setLinha(int pos_linha) {
        this.pos_linha = pos_linha;
    }

    @Override
    public /*@ pure @*/ int getColuna() {
        return pos_coluna;
    }

    @Override
    public void setColuna(int pos_coluna) {
        this.pos_coluna = pos_coluna;
    }
    
    //@ assignable isAlive;
    //@ ensures !this.isAlive;
    //Esse ensures da problema
    //ensures this.campo.getLocation(pos_linha, pos_coluna).getAtor() == null;
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
    public int inicializaFome(int maxFood){
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
    
    //Esse ensures tambem da problema
    /* requires idadeMinima >= 0;
      @ ensures \result == this.age >= idadeMinima;
      */
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
