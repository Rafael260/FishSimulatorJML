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
    protected Random random;
    protected boolean isAlive;
    protected int age;
    protected int nivelFome;
    protected int pos_linha;
    protected int pos_coluna;
    protected Field campo;
    
    /**
     * Constructor for objects of class Fish
     * @param campo é o campo onde todos se encontram
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
     * Função para saber se o ator está vivo
     * @return true, se o ator estiver vivo, false caso contrário
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
     * Esvazia a posição que o ator estava e marca como morto, para ser excluído da lista
     */        
    public void setMorto(){
        campo.limparPosicao(pos_linha, pos_coluna);
        isAlive = false;
    }
    
    /**
     * Inicia a fome de forma aleatória
     * @param maxFood é o número máximo de fome que o ator pode assumir
     * @return o número da fome do ator
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
     * O ator chama esse método quando encontra comida, aumenta seu nível da fome
     * @param valor é a quantidade de comida que o ator recebe
     * @param maxFood é o limite de comida para o ator
     */
    public void alimenta(int valor, int maxFood){
        nivelFome+=valor;
        if (nivelFome > maxFood){
            nivelFome = maxFood;
        }
        
    }
    
    /**
     * Move o ator de posição no tabuleiro
     * @param location é a localização atual
     * @param newLocation é a nova localização que o ator irá
     */
    public void mover(Location location, Location newLocation){
        campo.colocarAtor(this, newLocation);
        pos_linha = newLocation.getLinha();
        pos_coluna = newLocation.getColuna();
        campo.limparPosicao(location);
    }
    
    /**
     * Método usado para saber quando o ator pode ter filho
     * @param idadeMinima Idade mínima para gerar filhos
     * @return true ou false, dependendo dos valores
     */
    public boolean podeTerFilho(int idadeMinima){
        return age >= idadeMinima;
    }

    /**
     * Método responsável para dizer quantos filhos um ator poderá ter num determinado momento
     * É usado um randômico
     * @param idadeMinima é a condição para ter filho e chamar o método responsável para isso
     * @param probabilidade é o valor decimal para verificar as chances de ter filho
     * @param maxFilhos é o número máximo de filhos que o ator pode ter de uma vez
     * @return o número de filhos que irá nascer
     */
    public int numeroDeFilhos(int idadeMinima, double probabilidade, int maxFilhos){
        int numFilhos = 0;
        if (podeTerFilho(idadeMinima) && random.nextDouble() <= probabilidade){
            numFilhos = random.nextInt(maxFilhos) + 1;
        }
        return numFilhos;
    }
    
}
