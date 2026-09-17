# -*- coding: utf-8 -*-
"""
Created on Wed Mar  6 13:30:14 2019

@author: Nizziho
""" 

from time import *
from SimpleClausulas import *

from vartablasd import *
from ProblemaTrianFactor import *


    
def leeArchivoGlobal(Archivo):
    reader=open(Archivo,"r") 
    cadena = reader.readline()
    while cadena[0]=='c':
        cadena = reader.readline()
    
    cadena.strip()
    listaaux = cadena.split()
    print(listaaux)
    nvar = int(listaaux[2])
    nclaus = int(listaaux[3])
    print(nvar)
    while cadena[0]=='c':
        cadena = reader.readline()

    infor = simpleClausulas()
    for cadena in reader:
        if (cadena[0]!='c'):
            cadena.strip()
            listaux=cadena.split()
            listaux.pop()
            listaux = map(int,listaux)
            clausula= set(listaux)
            nc = set( map(lambda t: -t, clausula))

            infor.listaclausOriginal.append(clausula.copy())
            if not nc.intersection(clausula):
                infor.insertar(clausula, test = False)
            else:
               print("trivial ", clausula)

            if infor.contradict:
                print("contradiccion leyendo")
    
    return infor, nvar, nclaus
   
    
    



    
    

    
def main(prob, Previo=True, Mejora=False): #EDM
    

        


        # print("termino copia")


        prob.compile()
        config = prob.markovchainlogic()
        config = prob.markovchainvar(config)
        config = prob.markovchainvar(config, i=3)


        prob = prob.prob.copy()
    
        
        return prob
     






        


def treeWidth(prob):
    (orden,clusters,borr,posvar,child,parent) = triangulap(prob.pinicial)
    sizes = map(len,clusters)
    return(max(sizes))


def computetreewidhts(archivolee):
    archivogenera = "treewidths" + archivolee
    reader=open(archivolee,"r")
    writer=open(archivogenera,"w")
    writer.write("Problema;TreeWidth\n")
    for linea in reader:
            # i=i+1
            linea = linea.rstrip()
            if len(linea)>0:
                cadena = ""
                # param = linea.split()
                # nombre = param[0]
                # N1 = int(param[1])
                nombre=linea.strip()
                print(nombre)     
                (info, nvar, nclaus) = leeArchivoGlobal(nombre)
                
                cadena= nombre 
                prob = DeterministicDeletion(info) #EDM   #Último parámetro es 
                


                
                                    # prob = problemaTrianFactor(info,N1,Qev) #EDM   #Último parámetro es Q
                                    # main(prob)  #EDM 
                prob.inicia0()
                                    
                tw = treeWidth(prob)
                cadena = cadena + ";" + str(tw) + "\n"
                writer.write(cadena)
                                # ttotal += t5-t1

    writer.close()
    reader.close()



def borradocontablas(archivolee,  archivogenera="salida.csv",Q=30):
        
        reader=open(archivolee,"r")
        writer=open(archivogenera,"w")
        writer.write("Problema;Variable;Claúsulas;Q;MejoraLocal;Previo;PartirVars;TLectura;TBúsqueda;TTotal;SAT\n")
        ttotal = 0
        # i=0
        for linea in reader:
            # i=i+1
            linea = linea.rstrip()
            if len(linea)>0:
                cadena = ""
              
                nombre=linea.strip()
                print(nombre)     
                t1 = time()
                infor, nvar, nclaus = leeArchivoGlobal(nombre)
                
                prob = varpot()
                prob.computefromSimple(infor)

                t4 = time()
                                    # main(prob)  #EDM 
                bolSAT = main(prob) #EDM 
                t5 = time()
          
              
                                # ttotal += t5-t1
                # print(Q)
        # if i>0:
        #     print ("tiempo medio ", ttotal/i)cd cd 
        #     writer.write("tiempo medio " + str(ttotal/i)+"\n")
        writer.close()
        reader.close()    



    
# computetreewidhts("ListaCNF_Experimento.txt")
borradocontablas("entrada.txt","salida",Q=30)
# borradofacil("entrada",[5,10,15,20,25],[False],[False],[True],"resultado.txt")
# experimentimportance("entrada",20,"outimportance.txt")

