package rubix;


import java.awt.BorderLayout;
import java.awt.BasicStroke;
import java.awt.MouseInfo;
import java.awt.GridLayout;
import java.awt.Color;
import java.awt.Dimension;
import java.awt.event.MouseListener;
import java.awt.event.MouseMotionListener;
import java.awt.event.MouseEvent;
import java.awt.Color;
import java.awt.Font;
import java.awt.Dimension;
import java.awt.Graphics;
import java.awt.Graphics2D;
import java.awt.RenderingHints;
import java.awt.event.KeyEvent;
import java.awt.event.KeyListener;
import java.awt.image.BufferedImage;
import java.awt.image.DataBuffer;
import java.awt.image.WritableRaster;
import java.util.ArrayList;

import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JPanel;
import javax.swing.SwingUtilities;

import java.lang.Math; 


/**********
 * 
 * 
 *  This program was written as an application of a self learning process in Linear algebra
 *  
 *  3D rendering from scratch using principles of Linear algebra 
 *  
 *  with Rubix cube manipulation as an example
 * 
 * 
 * 
 *    @author Amine Bayoudh
 *  
 *           2023-2024
 *      
 *      
 */




// the program inherits the JPanel class
public class Rubix extends JPanel {

	
	//for JPanel
	private static final long serialVersionUID = 1L;
    //title
	static final String TITLE = "Amine Rubix cube";

	
	static final double[] origin_p  = {0,0,0,1};
	static final double[] origin_vx = {1,0,0,1};
	static final double[] origin_vy = {0,1,0,1};
	static final double[] origin_vz = {0,0,1,1};
	static final double   cube_x   = 250;
	static final double   cube_y   = 250;
	static final double   cube_z   = 3000;
	static double[]       cube_p   = {cube_x,cube_y,cube_z,1};
	static double[]       cube_vx  = {1,0,0,1};
	static double[]       cube_vy  = {0,1,0,1};
	static double[]       cube_vz  = {0,0,1,1};
	static final double   cube_l   = 600;
	
	//Constants for the inherited class
	static final int ROWS = 40;
	static final int COLUMNS = 40;
	static final int CELL_SIZE = 15;
	static final int CANVAS_WIDTH = COLUMNS * CELL_SIZE;
	static final int CANVAS_HEIGHT = ROWS * CELL_SIZE;
	static final int UPDATE_PER_SEC = 3;
	
	//window length and height
	static final double L = 500;
	static final double H = 500;
	static final Color orange = new Color(255,120,0);
	
	//camera position and position vector
	//and camera initial ORIENTATION VECTORS, an orthonormal basis
	static final double cx  = 250;
	static final double cy  = 250;
	static final double cz  = 0;
	
	//camera position vector
	static double[]     c_p = {cx,cy,cz,1}; //the 4th "1" might cause an error 
	
	static double[]     r_p = {(L/2),(H/2),0,1}; //this is the representation position ! 
	
	//camera orientation vectors
    static double[]     c_x = {1,0,0,1};
    static double[]     c_y = {0,1,0,1};
    static double[]     c_z = {0,0,1,1};
    
	static final double sx       = 1;  //scaling factor in x ???? we'll think about this later
	static final double sy       = 1;  //scaling factor in y ????
	
	
    static final double n = 700;    //the near plane
    static final double f = 10000;  //the far plane
	
	static ArrayList<object> objects = new ArrayList<object>();
	static       int ovx = 300;
	static       int ovy = 300;
	
	private rendering render;
	
	//main bufferedImage for rendering
	private BufferedImage canvas;
	
	//depth buffer
	double[][]     z_buffer   = new double[CANVAS_HEIGHT][CANVAS_WIDTH];
	//object/pixel record
	int  [][]     codex      = new int  [CANVAS_HEIGHT][CANVAS_WIDTH];
	
	static int[]  angle      = new int[9];
	static int[] unallowed   = new int[9];

	
	
	//coordinates in vector form relative to the center point of the cube (the rows are the vectors) 
	//relative to the way we have set the standard basis to be (Z+ being depth and Y+ going downwards)
	// ordered as such F-R-B-L-U-D
	// homogeneous bias "1" is to be added later
	static double[][] cube = {   
			
			{-1,-1,-1 ,0},
			{ 1,-1,-1 ,0},
			{ 1, 1,-1 ,0},
			{-1, 1,-1 ,0},
			
			{ 1,-1,-1 ,0},
			{ 1, 1,-1 ,0},
			{ 1, 1, 1 ,0},
			{ 1,-1, 1 ,0},
			
			{-1,-1, 1, 0},
			{ 1,-1, 1, 0},
			{ 1, 1, 1, 0},
			{-1, 1, 1, 0},
			
			{-1,-1,-1 ,0},
			{-1, 1,-1 ,0},
			{-1, 1, 1 ,0},
			{-1,-1, 1 ,0},
			
			{-1,-1,-1 ,0},
			{ 1,-1,-1 ,0},
			{ 1,-1, 1 ,0},
			{-1,-1, 1 ,0},
			
			{-1, 1,-1 ,0},
			{ 1, 1,-1 ,0},
			{ 1, 1, 1 ,0},
			{-1, 1, 1 ,0}

			
	};
	
	
	//correction table for square representation
	static double[][] cube_correction = {
			{ 0,0,1,0},
			
			{-1,0,0,0},
			
			{0,0,-1,0},
			
			{1,0,0,0},
			
			{0,1,0,0},
			
			{0,-1,0,0}
	};
	
	
	///// Mathematical Core +++++++++++++++++ /////////////////////////////////////////////////////////////////////
	
	//perspective matrix
    static double[] perspective     = {   //P
    		
            n,  0,  0,         0,
            0,  n,  0,         0,
            0,  0,  f+n,  -(f*n),
            0,  0,  1,         0    
            
            };

    //screen representation matrix
    static double[] representation  = {   //R             <- for visualisation in the coordinate system of the screen

            sx, 0,  0,       L/2,   
            0,  sy, 0,       H/2,
            0,  0,  1,         0,
            0,  0,  0,         1,
            
            };

    static double[] RP              = {   //R*P

            sx*n,  0,     L/2,        0,
            0,     sy*n,  H/2,        0,
            0,     0,     f+n,   -(f*n),
            0,     0,       1,        0    

            };
    
    //the inverse of the final representation matrix
    static double[] RP_inv          = {   //(R*P)-1

            1/(sx*n),  0,         0,        -(L/2)/(sx*n),        
            0,         1/(sy*n),  0,        -(H/2)/(sy*n),        
            0,         0,         0,                    1,  
            0,         0,        -1/(f*n),    (f+n)/(f*n)             

            };

    static double[] rep      = new double[16];    // holds the final representation matrix  RP(C-1)   <-- this is an invertible matrix 
    static double[] rep_inv  = new double[16];    // holds the inverse of this matrix       C(RP-1)
    
    
    //simple math
    static double squared_distance(double[] v1,double[] v2) {
    	
    	double out;
    	
    	out = ((v2[0]-v1[0])*(v2[0]-v1[0]))+
    		  ((v2[1]-v1[1])*(v2[1]-v1[1]))+
    		  ((v2[2]-v1[2])*(v2[2]-v1[2]));
    	
    	return out;
    	
        }
        
        static double squared_length_3(double v1[]) {
        	double out;
        	
        	out = (v1[0]*v1[0])+(v1[1]*v1[1])+(v1[2]*v1[2]);
        	
        	return out;
        }
        
        
        static double dot_product_h(double v1[],double v2[]) {
        	double tv1[] = new double[4];
        	double tv2[] = new double[4];
        	
        	
        	tv1[0] = v1[0]/v1[3];
        	tv1[1] = v1[1]/v1[3];
        	tv1[2] = v1[2]/v1[3];
        	
        	tv2[0] = v2[0]/v2[3];
        	tv2[1] = v2[1]/v2[3];
        	tv2[2] = v2[2]/v2[3];
        	
        	double o = (tv1[0]*tv2[0])+
        			  (tv1[1]*tv2[1])+
        			  (tv1[2]*tv2[2]);
        	return o;
        			
        }
        
        static double dot_product_3(double v1[],double v2[]) {

        	
        	double o = (v1[0]*v2[0])+
        			  (v1[1]*v2[1])+
        			  (v1[2]*v2[2]);
        	return o;
        			
        }
        
        static double squared_distance_h(double[] v1,double[] v2) {
        	
    	double out ;
    	
    	//remove the homogeneous component
    	
    	double tv1[] = new double[4];
    	double tv2[] = new double[4];
    	
    	
    	tv1[0] = v1[0]/v1[3];
    	tv1[1] = v1[1]/v1[3];
    	tv1[2] = v1[2]/v1[3];
    	
    	tv2[0] = v2[0]/v2[3];
    	tv2[1] = v2[1]/v2[3];
    	tv2[2] = v2[2]/v2[3];
    	
    	out = ((tv2[0]-tv1[0])*(tv2[0]-tv1[0]))+
    		  ((tv2[1]-tv1[1])*(tv2[1]-tv1[1]))+
    		  ((tv2[2]-tv1[2])*(tv2[2]-tv1[2]));
    	
    	return Math.sqrt(out);
    	
        }

        
        //matrix * vector multiplication  returns a 4 element vector
        static double[] mv(double[] matrix, double[] vector) {
    	
    	double[] vout = new double[4];
    	
    	vout[0] = matrix[0+(0*4)]*vector[0]  +  matrix[1+(0*4)]*vector[1]  +  matrix[2+(0*4)]*vector[2]  +  matrix[3+(0*4)]*vector[3];
    	vout[1] = matrix[0+(1*4)]*vector[0]  +  matrix[1+(1*4)]*vector[1]  +  matrix[2+(1*4)]*vector[2]  +  matrix[3+(1*4)]*vector[3];
    	vout[2] = matrix[0+(2*4)]*vector[0]  +  matrix[1+(2*4)]*vector[1]  +  matrix[2+(2*4)]*vector[2]  +  matrix[3+(2*4)]*vector[3];
    	vout[3] = matrix[0+(3*4)]*vector[0]  +  matrix[1+(3*4)]*vector[1]  +  matrix[2+(3*4)]*vector[2]  +  matrix[3+(3*4)]*vector[3];
    	
    	return vout;
    	 			
        }

        //matrix * matrix multiplication returns a 4*4 matrix (16 element double array)
        static double[] mm(double[] matrix, double[] matrix0) {
    	
    	double[] mout  = new double[16];
    	double[] tempv = new double[4];
    	
    	for(int i=0;i<4;i++) {
    	tempv[0] = matrix0[(0*4)+i];
    	tempv[1] = matrix0[(1*4)+i];
    	tempv[2] = matrix0[(2*4)+i];
    	tempv[3] = matrix0[(3*4)+i];
    	tempv    = mv(matrix,tempv);
        mout[(0*4)+i] = tempv[0];
        mout[(1*4)+i] = tempv[1];
        mout[(2*4)+i] = tempv[2];
        mout[(3*4)+i] = tempv[3];
    	}
    	
    	return mout;
    	 			
        }



        //sets the representation and de-represenation matrices 
        // Rep = RP(C-1)    and DeRep = C((RP)-1)
        static void   set_rep () {
    	
           double[] c1 = {
        		   
        		 c_x[0],  c_y[0], c_z[0], 0,
        		 c_x[1],  c_y[1], c_z[1], 0,
        		 c_x[2],  c_y[2], c_z[2], 0,
        		      0,       0,      0, 1
           };
           
           double[] c2 = {
        		   
        		 1,0,0,c_p[0],
        		 0,1,0,c_p[1],
        		 0,0,1,c_p[2],
        		 0,0,0,1  
           };
           
           double[] c2_inv = {
        		   
        		 1,0,0,-c_p[0],
        		 0,1,0,-c_p[1],
        		 0,0,1,-c_p[2],
        		 0,0,0,1  
           };
           
           double[] c1_inv = {  //equal to C1 transpose because all the vectors form an orthonormal basis 
        		 c_x[0],c_x[1],c_x[2],  0,
        		 c_y[0],c_y[1],c_y[2],  0,
        		 c_z[0],c_z[1],c_z[2],  0,
        		      0,     0,     0,  1
        		   
           };
           
           double[] c      = new double[16];  c      = mm(c2,c1);
           double[] c_inv  = new double[16];  c_inv  = mm(c1_inv,c2_inv);
           
           rep     = mm(RP,c_inv);
           rep_inv = mm(c,RP_inv);
            
    	
           }



        // 0-z   1-x   2-y
        // return a 4x4 rotation matrix
        // this method calculates rotation matrix
        static double[] calculate_rotation_matrix(double[] p,int a,double angle) {
    	
    	double[]   htemp      = new double[16];
    	double[]   rot_matrix = new double[16];
    	
    	double rad = Math.toRadians(angle);
    	
        double[] to_standard     = {
                1,0,0,-p[0],
                0,1,0,-p[1],
                0,0,1,-p[2],
                0,0,0,    1,

              };
        
        double[] rotate_x         = {
                1  ,0                      ,0                          ,0,
                0  ,Math.cos(rad)   ,Math.sin(rad)       ,0,
                0  ,-Math.sin(rad)  ,Math.cos(rad)       ,0,
                0  ,0                      ,0                          ,1

              };
        
        double[] rotate_y         = {
                Math.cos(rad)  ,0       ,-Math.sin(rad)       ,0,
                0                     ,1       ,0                           ,0,
                Math.sin(rad)  ,0       ,Math.cos(rad)        ,0,
                0                     ,0       ,0                           ,1

              };
        
        double[] rotate_z         = {
        		Math.cos(rad)  ,-Math.sin(rad)  ,0                          ,0,
        		Math.sin(rad)  ,Math.cos(rad)   ,0                          ,0,
                0                     ,0                      ,1                          ,0,
                0                     ,0                      ,0                          ,1

              };
        
        if     (a==0) rot_matrix = rotate_z;
        else if(a==1) rot_matrix = rotate_x;
        else if(a==2) rot_matrix = rotate_y;
        
        double[] to_position     = {
                1,0,0,p[0],
                0,1,0,p[1],
                0,0,1,p[2],
                0,0,0,   1,

              };
        /*
        htemp = mm(to_standard,rep_inv);
        htemp = mm(rot_matrix,htemp);
        htemp = mm(to_position,htemp);
        htemp = mm(rep,htemp); 
        */
        
        htemp = mm(rot_matrix,to_standard);
        htemp = mm(to_position,htemp);   
        
        
        return htemp;

        
        }
        
        //calculates rotation matrix relative to a specific coordinate space (a different Basis)
        static double[] calculate_rotation_matrix(double[] p,double[] vx,double[] vy,double[] vz,int a,double angle) {
        
        
    	double[]   htemp      = new double[16];
    	double[]   rot_matrix = new double[16];
    	
    	double rad = Math.toRadians(angle);
    	

    	
        double[] inv_matrix         = {

        		vx[0],vx[1],vx[2],    0,
        		vy[0],vy[1],vy[2],    0,
        		vz[0],vz[1],vz[2],    0,
        		    0,    0,    0,    1,

              };
        
        double[] matrix         = {

        		vx[0],vy[0],vz[0],0,
        		vx[1],vy[1],vz[1],0,
        		vx[2],vy[2],vz[2],0,
        		    0,    0,    0,1,

              };
        
        double[] to_standard     = {
                1,0,0,-p[0],
                0,1,0,-p[1],
                0,0,1,-p[2],
                0,0,0,    1,

              };
        
        double[] rotate_x         = {
                1  ,0                      ,0                          ,0,
                0  ,Math.cos(rad)   ,Math.sin(rad)       ,0,
                0  ,-Math.sin(rad)  ,Math.cos(rad)       ,0,
                0  ,0                      ,0                          ,1

              };
        
        double[] rotate_y         = {
                Math.cos(rad)  ,0       ,-Math.sin(rad)       ,0,
                0                     ,1       ,0                           ,0,
                Math.sin(rad)  ,0       ,Math.cos(rad)        ,0,
                0                     ,0       ,0                           ,1

              };
        
        double[] rotate_z         = {
        		Math.cos(rad)  ,-Math.sin(rad)  ,0                          ,0,
        		Math.sin(rad)  ,Math.cos(rad)   ,0                          ,0,
                0                     ,0                      ,1                          ,0,
                0                     ,0                      ,0                          ,1

              };
        
        if     (a==0) rot_matrix = rotate_z;
        else if(a==1) rot_matrix = rotate_x;
        else if(a==2) rot_matrix = rotate_y;
        
        double[] to_position     = {
                1,0,0,p[0],
                0,1,0,p[1],
                0,0,1,p[2],
                0,0,0,   1,

              };

        
        htemp = mm(inv_matrix,to_standard);
        htemp = mm(rot_matrix,htemp);
        htemp = mm(matrix    ,htemp);
        htemp = mm(to_position,htemp);   
        
        
        return htemp;

        
        }
        
        
        // calculates an inverse matrix , to perform a Basis change , relative to a position and basis vectors
        static double[] calculate_inv_matrix(double[] p,double[] vx,double[] vy,double[] vz) {
        	
        	double[]   htemp      = new double[16];
        	
            double[] to_standard     = {
                    1,0,0,-p[0],
                    0,1,0,-p[1],
                    0,0,1,-p[2],
                    0,0,0,    1,

                  };
            
            double[] inv_matrix         = {

            		vx[0],vx[1],vx[2],    0,
            		vy[0],vy[1],vy[2],    0,
            		vz[0],vz[1],vz[2],    0,
            		    0,    0,    0,    1,

                  };
       
            
            double[] to_position     = {
                    1,0,0,p[0],
                    0,1,0,p[1],
                    0,0,1,p[2],
                    0,0,0,   1,

                  };
            
            htemp = mm(inv_matrix,to_standard);  
            
            
            return htemp;

            
            }
        
        
        //calculate rotation matrix for the Camera+++
        static double[] calculate_rotation_matrix_camera(double[] p,int a,double angle) {
        	
    	double[]   htemp      = new double[16];
    	double[]   rot_matrix = new double[16];
    	
    	double rad =  Math.toRadians(angle);
    	
        double[] to_standard     = {
                1,0,0,-p[0],
                0,1,0,-p[1],
                0,0,1,-p[2],
                0,0,0,    1,

              };
        
        double[] rotate_x         = {
                1  ,0                      ,0                          ,0,
                0  ,Math.cos(rad)   ,Math.sin(rad)       ,0,
                0  ,-Math.sin(rad)  ,Math.cos(rad)       ,0,
                0  ,0                      ,0                          ,1

              };
        
        double[] rotate_y         = {
                Math.cos(rad)  ,0       ,-Math.sin(rad)       ,0,
                0                     ,1       ,0                           ,0,
                Math.sin(rad)  ,0       ,Math.cos(rad)        ,0,
                0                     ,0       ,0                           ,1

              };
        
        double[] rotate_z         = {
        		Math.cos(rad)  ,-Math.sin(rad)  ,0                          ,0,
        		Math.sin(rad)  ,Math.cos(rad)   ,0                          ,0,
                0                     ,0                      ,1                          ,0,
                0                     ,0                      ,0                          ,1

              };
        
        if(a==0)      rot_matrix = rotate_x;
        else if(a==1) rot_matrix = rotate_y;
        else if(a==2) rot_matrix = rotate_z;
        
        double[] to_position     = {
                1,0,0,p[0],
                0,1,0,p[1],
                0,0,1,p[2],
                0,0,0,   1,

              };
        
        htemp = mm(rot_matrix,to_standard);
        htemp = mm(to_position,htemp);
        
        
        return htemp;

        
        }
        
    	//add two 4x4 vectors
    	static double[]  av(double[] v1,double[] v2) {
    		
    		double[] temp = new double[4];
    		temp[0]=v1[0]+v2[0];
    		temp[1]=v1[1]+v2[1];
    		temp[2]=v1[2]+v2[2];
    		temp[3]=v1[3]+v2[3];
    		return temp;
    	}
    	
    	//add and scale both vectors
    	static double[]  av(double[] v1,double f1,double[] v2,double f2) {
    		
    		double[] temp = new double[4];
    		temp[0]=(v1[0]*f1)+(v2[0]*f2);
    		temp[1]=(v1[1]*f1)+(v2[1]*f2);
    		temp[2]=(v1[2]*f1)+(v2[2]*f2);
    		temp[3]=(v1[3]*f1)+(v2[3]*f2);
    		return temp;
    	}
    	
    	//average vector between two vectors
    	static double[]  v_average(double[] v1,double[] v2) {
    		
    		double[] temp = new double[4];
    		temp[0]=(v1[0]+v2[0])/2;
    		temp[1]=(v1[1]+v2[1])/2;
    		temp[2]=(v1[2]+v2[2])/2;
    		temp[3]=(v1[3]+v2[3])/2;
    		return temp;
    	}
    	
    	//substract two 4x4 vectors and multiply the latter by a factor f
    	static double[]  sv(double[] v1,double[] v2,double f) {
    		
    		double[] temp = new double[4];
    		temp[0]=v1[0]-(v2[0]*f);
    		temp[1]=v1[1]-(v2[1]*f);
    		temp[2]=v1[2]-(v2[2]*f);
    		temp[3]=v1[3]-(v2[3]*f);
    		return temp;
    	}
    	
    	//scale vector
        static double[]  scv(double[] v2,double f) {
    		
    		double[] temp = new double[4];
    		temp[0]=(v2[0]*f);
    		temp[1]=(v2[1]*f);
    		temp[2]=(v2[2]*f);
    		temp[3]=(v2[3]*f);
    		return temp;
    	}
        
        
        
 //////////////////////////////////////////////////////////////////////////////////////////////////////////////
        
        
	//class to store basic polygons (smallest rendering unit)
    static class polygone {
    	   public Color     color;
    	   public double[][] vector = new double[3][4];
    	   
    	   
    	   public double[]   center;   // <--------------------
    	   public double     distance; //distance from camera center point
    	   public int       attribute;
    	   public int       face;
    	   
    }
   
   //larger objects that contain multiple polygons
   static class object {
	       public ArrayList<polygone> content = new ArrayList<polygone>();
	       
	       
	       public double[]  center;   // <------------------------
	       public double    distance; //distance from camera center point
	       public int      attribute;
   }
	
	// Constructor to initialize the UI components and rendering object
	public Rubix() {
		
		// create UI components
		setLayout(new BorderLayout());
		render = new rendering();
		render.setSize(new Dimension(CANVAS_WIDTH,CANVAS_HEIGHT));
		add(render, BorderLayout.CENTER);

	}
	
    
    
	//Create an orthonormal basis (or orthonormalize the current basis even more relative to v1
	static void gram_schmidt() {
		//normalize v1
		cube_vz = scv(cube_vz,1/Math.sqrt(squared_length_3(cube_vz))); cube_vz[3]=1;
		
	    cube_vx = sv (cube_vx,cube_vz,dot_product_3(cube_vz,cube_vx)); 
	    cube_vx = scv(cube_vx,1/Math.sqrt(squared_length_3(cube_vx))); cube_vx[3]=1;
	    
	    
	    cube_vy = sv (cube_vy,cube_vz,dot_product_3(cube_vy,cube_vz)); 
	    cube_vy = sv (cube_vy,cube_vx,dot_product_3(cube_vy,cube_vx)); 
	    cube_vy = scv(cube_vy,1/Math.sqrt(squared_length_3(cube_vy))); cube_vy[3]=1;
	    
	    //System.out.println("gram output : "+squared_length_3(cube_vz)+"  "+squared_length_3(cube_vx)+"  "+squared_length_3(cube_vy)+"  ");
	    
	}
	
	
	
	// Refresh the display. Called back via repaint(), which invoke the paintComponent()
	private void Draw(Graphics g) {
		//draw game objects
        ////// DRAW STUFF 
		
		z_buffer = new double[CANVAS_HEIGHT][CANVAS_WIDTH];
		codex    = new int  [CANVAS_HEIGHT][CANVAS_WIDTH];
		
		BufferedImage canvas = new BufferedImage(CANVAS_WIDTH, CANVAS_HEIGHT, BufferedImage.TYPE_INT_ARGB);
		for(int i=0;i<CANVAS_HEIGHT;i++) for(int j=0;j<CANVAS_WIDTH;j++) z_buffer[i][j] = 9999999;
		WritableRaster raster = canvas.getRaster();
		DataBuffer dataBuffer = raster.getDataBuffer();
		
		
		/*
		double[][] axle_points = new double [3][4];
		double[]   cube_p_pos  = new double [4];
		
		cube_p_pos = mv(rep,cube_p);
		cube_p_pos[0]/=cube_p_pos[3];
		cube_p_pos[1]/=cube_p_pos[3];
		cube_p_pos[2]/=cube_p_pos[3];
		
		axle_points[0]= scv(cube_vz,300); axle_points[0][3]=1;
		axle_points[1]= scv(cube_vx,300); axle_points[1][3]=1;
		axle_points[2]= scv(cube_vy,300); axle_points[2][3]=1;
		
		ArrayList<Color> axle_colors = new ArrayList<Color>();
		
		axle_colors.add(Color.red);
		axle_colors.add(Color.green);
		axle_colors.add(Color.blue);
		
		
		for(int i=0;i<3;i++) {
			    axle_points[i]=av(cube_p,axle_points[i]); axle_points[i][3]=1;
				axle_points[i]=mv(rep,axle_points[i]);
				axle_points[i][0]/=axle_points[i][3];
				axle_points[i][1]/=axle_points[i][3];
				axle_points[i][2]/=axle_points[i][3];
		}  */
		
		
        for(int i=objects.size()-1;i>=0;i--) {
         
       
        	
        	for(int j=objects.get(i).content.size()-1;j>=0;j--) {
        	
        	int[] xp = new int[3];
        	int[] yp = new int[3];
        	int[] zp = new int[3];
        	
        	polygone temp = new polygone();
        	
        	temp.vector[0] = mv(rep,objects.get(i).content.get(j).vector[0]);
        	temp.vector[1] = mv(rep,objects.get(i).content.get(j).vector[1]);
        	temp.vector[2] = mv(rep,objects.get(i).content.get(j).vector[2]);
        	
        	for(int k=0;k<3;k++) {
        		      		
        		xp[k]=(int) Math.round((temp.vector[k][0]/temp.vector[k][3]));
        		yp[k]=(int) Math.round((temp.vector[k][1]/temp.vector[k][3]));
        		zp[k]=(int) Math.round(                   temp.vector[k][3] );
        		

        	}
        	
        	g.setColor(objects.get(i).content.get(j).color);
            
        	int local_codex = 1 + objects.get(i).attribute + (objects.get(i).content.get(j).face*100);
        	draw_triangle(dataBuffer,z_buffer,codex,local_codex, xp, yp, zp,objects.get(i).content.get(j).color.getRGB());
        	
        	//g.fillPolygon(xp,yp,3);
 	
        }         
        }
        	 Graphics2D g2 = (Graphics2D) g;
        	 g2.drawImage(canvas, null, null);
        	 Font f = new Font("default", Font.BOLD, 16);
        	 g.setFont(f);
        	 g.setColor(Color.white);
        	 g.drawString("Amine Bayoudh - 2023", 300, 450);
        	 //BasicStroke bs = new BasicStroke(10);
        	 //g2.setStroke(bs);
        	 //for(int i=0;i<3;i++) { g2.setColor(axle_colors.get(i)); g2.drawLine((int)cube_p_pos[0],(int)cube_p_pos[1],(int)axle_points[i][0],(int)axle_points[i][1]);  }
        	
		
	}
	
	/*
	static void rep_all() {
   	 for(object obj : objects) {
   	  for(polygone i : obj.content) {
   		 double[] cp = {0,0,0,0};
   		 for(int j = 0;j<4;j++) {i.vector[j]=mv(rep,i.vector[j]);
   		                         cp= av(cp,i.vector[j]);
   		                         
   		 }      cp = scv(cp,0.25);
   		        i.center   =cp;                    
   		        i.distance =squared_distance_h(cp,r_p);
   	   }
   	  }
    }
	
	static void derep_all() {
	   	 for(object obj : objects) {
	      	  for(polygone i : obj.content) {
	      		 double[] cp = {0,0,0,0};
	      		 for(int j = 0;j<4;j++) {i.vector[j]=mv(rep_inv,i.vector[j]);
	      		                         cp= av(cp,i.vector[j]);
	      		                         
	      		 }                       cp= scv(cp,0.25); 
	      		  i.center   =cp;
	      		  i.distance =squared_distance_h(cp,r_p);
	      	   }
	      	  }
	    }
	*/
	
	//sets distances relative to the observation point , to order objects relative to their respective depth
	static void set_distances() {
		 
	   	 for(object obj : objects) {
	   		 
	   	  double[] ocp ={0,0,0,0};
	   	  double   oc  =0;
	   	  
	   	  for(polygone i : obj.content) {
	   		 double[] cp = {0,0,0,0};

	   		 for(int j = 0;j<3;j++) {
	   		                         cp= av(cp,i.vector[j]);
	   		                         
	   		 }      cp[0]=cp[0]/3; cp[1]=cp[1]/3; cp[2]=cp[2]/3; cp[3]=cp[3]/3;  		  
	   		        i.center   =cp;                    
	   		        i.distance =squared_distance_h(cp,c_p);
	   		        if(i.attribute=='b') {
	   		        ocp=av(ocp,cp);
	   		        oc++;
	   		        }
	   		        
	   	   }        
	   	            ocp=scv(ocp,(1/oc));
	   	            obj.center = ocp;
	   	            obj.distance=squared_distance_h(ocp,c_p);
	   	            
	   	  }
	    }
	
	
  	 //reorder the array list elements according to new Z values
	// reorders objects to obtain depth
		static void reorder_objects() {
			
		   	 for(int i=1;i<objects.size();i++) {
		   		 if(objects.get(i).distance < objects.get(i-1).distance) {
		   			 for(int j=i;j>0;j--) {
		   				 
		   				// double[] svo = new double[4];
		   				// double[] svc = new double[4];
		   				// svo = sv(objects.get(j).center,objects.get(j-1).center, 1);
		   				// svc = sv(c_p,objects.get(j).center, 1); 
		   				 		 
		   				 if(objects.get(j).distance < objects.get(j-1).distance)
		   					   { //poorly optimized , we'll fixe it later
		   					   //System.out.println("swapped");
		   					   object temp = new object();
		   					   temp = objects.get(j-1);
		   					   objects.set(j-1, objects.get(j)); // First half of swap.
		   					   objects.set(j  , temp);            // Final operation for swap.
		   				 }
		   				 
		   			 } 
		   		 }
		   	 }
			
		}
	  	 //reorder the array list elements according to new Z values 
			static void reorder_content(object obj) {
				
				
			   	 for(int i=1;i<obj.content.size();i++) {
			   		 if(Math.round(obj.content.get(i).distance) < (Math.round(obj.content.get(i-1).distance)-10)) {
			   			 for(int j=i;j>0;j--) {
			   				 if(Math.round(obj.content.get(j).distance) < (Math.round(obj.content.get(j-1).distance-10))) { //poorly optimized , we'll fixe it later
			   					   //System.out.println("swapped");
			   					   polygone temp = new polygone();
			   					   temp = obj.content.get(j-1);
			   					   obj.content.set(j-1, obj.content.get(j)); // First half of swap.
			   					   obj.content.set(j  , temp);            // Final operation for swap.
			   				 }
			   			 } 
			   		 }
			   	 }
				
			}
		
	
		
			// 0-z   1-x   2-y
			// rotates all the objects 
		static void rotate_all(int a,double angle) {
			
			 double[] rotation_matrix = new double[16];
			 rotation_matrix = calculate_rotation_matrix(cube_p,a,angle);
			 
			 for(object o : objects) {
	    	 for(polygone i : o.content) {
	    		 for(int j = 0;j<3;j++) i.vector[j]=mv(rotation_matrix,i.vector[j]);                  
	    	 }   
	    	       reorder_content(o);
			 }
	    	 
	    	 
	    	 rotation_matrix = calculate_rotation_matrix(origin_p,a,angle);
	    	 cube_vx = mv(rotation_matrix,cube_vx);
	    	 cube_vy = mv(rotation_matrix,cube_vy);
	    	 cube_vz = mv(rotation_matrix,cube_vz);
	    	 gram_schmidt(); 
	    	 

		}
		
		// rotates the reference vectors of the rubix cube 
		
		static void rotate_all_reference(int a,double angle) {
			
			 double[] rotation_matrix = new double[16];	 
			 rotation_matrix         = calculate_rotation_matrix(origin_p,cube_vx,cube_vy,cube_vz,a,angle);
			 
	    	 cube_vx = mv(rotation_matrix,cube_vx);
	    	 cube_vy = mv(rotation_matrix,cube_vy);
	    	 cube_vz = mv(rotation_matrix,cube_vz);
	    	 gram_schmidt();
	    	 

		}
		    // 0-z   1-x   2-y
		// rotates rubix cube segments 
		static void rotate_at_x(int a,double angle) {
			
			 double[] rot_axle = new double[4];
			 double[] rotation_matrix = new double[16];
			 double[]      inv_matrix = new double[16];
			 inv_matrix              = calculate_inv_matrix     (cube_p,cube_vx,cube_vy,cube_vz);
			 
			 double[]      rot_orig   = new double[4];
			 
			      if((a/3)==0) rot_axle = cube_vz;
			 else if((a/3)==1) rot_axle = cube_vx;
			 else if((a/3)==2) rot_axle = cube_vy;     
			      
			 rot_orig                = sv(cube_p,rot_axle,((a%3)-1)*(cube_l/3));
			 
			 
			 rotation_matrix         = calculate_rotation_matrix(rot_orig,cube_vx,cube_vy,cube_vz,(a/3),angle);
			 
			 
			 for(object o : objects) {
		     
			 double[] ocenter = new double[4];
			 ocenter = mv(inv_matrix,o.center);
			 
			 int trg=a/3;
			      if(trg==0) trg=2;
			 else if(trg==1) trg=0;
			 else if(trg==2) trg=1;
			 
			 if(Math.abs(ocenter[trg]-(((a%3)-1)*(cube_l/3)))<30) {
				 
			 object_activated[o.attribute]=1;
			 object_rot_orig[o.attribute]=rot_orig;
			 
	    	 for(polygone i : o.content) {
	    		 for(int j = 0;j<3;j++) i.vector[j]=mv(rotation_matrix,i.vector[j]);
	    	 }     
	    	       reorder_content(o);
			 } 
			 }

		}
		
		//rotates the camera (observation angle)
		static void rotate_camera(int a,double angle) {
			
			 double[] rotation_matrix = new double[16];
			 rotation_matrix = calculate_rotation_matrix_camera(cube_p,a,angle);
			 double[] c2 = {
		    		   
		    		 1,0,0,c_p[0],
		    		 0,1,0,c_p[1],
		    		 0,0,1,c_p[2],
		    		 0,0,0,1  
		       };
			 c_x = mv(rotation_matrix,mv(c2,c_x));
			 c_y = mv(rotation_matrix,mv(c2,c_y));
			 c_z = mv(rotation_matrix,mv(c2,c_z));
			 c_p = mv(rotation_matrix,c_p);
			 
			 
			 double[] c2p = {
		    		   
		    		 1,0,0,-c_p[0],
		    		 0,1,0,-c_p[1],
		    		 0,0,1,-c_p[2],
		    		 0,0,0,1  
		       };
			 
			 c_x = mv(c2p,c_x);
			 c_y = mv(c2p,c_y);
			 c_z = mv(c2p,c_z);
	    	 

		}
		
	    // draws a line between (x1, y1) and (x2, y2) , with a line width of 2 to 3 pixels
		// can certainly be optimized 
	     static void drawLine(DataBuffer img, double[][] zbuff,int[][] codex,int lc, int col,double x1, double y1, double z1, double x2, double y2, double z2) {

	        double dx = Math.abs(x2 - x1);
	        double dy = Math.abs(y2 - y1);
	        double dz = Math.abs(z2 - z1);

	        int x, y;
	        
	        double z;
	        
	        int xSign = x1 < x2 ? 1 : -1;
	        int ySign = y1 < y2 ? 1 : -1;
	        int zSign = z1 < z2 ? 1 : -1;

	        if (dx >= dy) {
	            double slope = dy / dx;
	            double error = slope - 0.5f;
	            y = (int) y1;

	            for (x = (int) x1; x != (int) x2; x += xSign) {
	            	
	            	
	            	z = z1  +  (zSign*(dz*(((x-x1)*xSign))/dx))   ;
	            	
	            	//Systeout.println(z1);
	            	
	            	double[] comp_vect = {x,y,z,1};
	            	double[] cam_vect  = {255,255,0,1};
	            	
	            	double dist      = squared_distance_h(comp_vect, cam_vect);
	            	
	            	int allow = 0;
	            	if((codex[y][x]==lc) && (col!=Color.black.getRGB())) {allow=1;}
	            	

	            	if((dist <= (zbuff[y][x]+2))||(allow>0)) {
	            		
	            	zbuff[y][x] = dist;
	            	codex[y][x] = lc;
	            	img.setElem(x  + ((y)*CANVAS_WIDTH), col);
	            	img.setElem(x  + ((y+1)*CANVAS_WIDTH), col);
	                img.setElem(x+1+ ((y)*CANVAS_WIDTH), col);
	                img.setElem(x-1+ ((y)*CANVAS_WIDTH), col);
	                img.setElem(x  + ((y-1)*CANVAS_WIDTH), col);
	                
	            	}
	                
	                error += slope;
	                if (error > 0.5) {
	                    y += ySign;
	                    error -= 1.0;
	                }
	            }
	        } else {
	            double slope = dx / dy;
	            double error = slope - 0.5f;
	            x = (int) x1;

	            for (y = (int) y1; y != (int) y2; y += ySign) {
	            	
	            	z = z1+(zSign*(dz*(((y-y1)*ySign)/dy)));
	            	
	            	double[] comp_vect = {x,y,z,1};
	            	double[] cam_vect  = {250,250,0,1};
	            	
	            	double dist      = squared_distance_h(comp_vect, cam_vect);
	            	
	            	int allow = 0;
	            	if((codex[y][x]==lc) && (col!=Color.black.getRGB())) allow=1;
	            	
	            	if((dist <= (zbuff[y][x]+2))||(allow>0)) {
	            		
		            zbuff[y][x] = dist;
		            codex[y][x] = lc;
	            	img.setElem(x  + ((y)*CANVAS_WIDTH), col);
	            	img.setElem(x  + ((y+1)*CANVAS_WIDTH), col);
	                img.setElem(x+1+ ((y)*CANVAS_WIDTH), col);
	                img.setElem(x-1+ ((y)*CANVAS_WIDTH), col);
	                img.setElem(x  + ((y-1)*CANVAS_WIDTH), col);
	                
	            	}
	            	
	                error += slope;
	                if (error > 0.5) {
	                    x += xSign;
	                    error -= 1.0;
	                }
	            }
	        }
	    }
	    
	    
		static void draw_triangle(DataBuffer bi, double[][] zbuff,int[][] codex,int lc, int[] xp,int[] yp,int[] zp,int c) {
			double[] v1 = new double[3];
			double[] v2 = new double[3];
			
			v1[0] = (xp[2]-xp[0]);
			v1[1] = (yp[2]-yp[0]);
			v1[2] = (zp[2]-zp[0]);
			
			v2[0] = (xp[2]-xp[1]);
			v2[1] = (yp[2]-yp[1]);
			v2[2] = (zp[2]-zp[1]);
			
			double lv1 = Math.sqrt((v1[0]*v1[0])+(v1[1]*v1[1])+(v1[2]*v1[2])) ;

			
			
			for(int j=0;j<Math.round(lv1);j++) {
				
				drawLine(bi,zbuff, codex, lc, c,
						
						             (xp[0]+((v1[0]*j)/lv1)) ,(yp[0]+((v1[1]*j)/lv1)), (zp[0]+((v1[2]*j)/lv1)),
						
						             (xp[1]+((v2[0]*j)/lv1)) ,(yp[1]+((v2[1]*j)/lv1)), (zp[1]+((v2[2]*j)/lv1))
						             
						             );			   
				
			}
			
		}
	
	    
		static int[]       object_activated = new int[99];
		static double[][]  object_rot_orig  = new double[99][4];
		
		
		// flag variables for Cube manipulation coordination 
		static int   primer     = 999;
		static int   dir_sign   = 0;
		static int   action     = 0;
		static int   activation = 0;             //truly activated axle in this area   0-disactivated , -1, 1
		static int   vector  = 0; //                                    0-disactivated , 1-x          , 2-y
		static int   mx=0,my=0;
	
	// Custom drawing panel, written as an inner class
	class rendering extends JPanel implements KeyListener,MouseListener,MouseMotionListener {

		private static final long serialVersionUID = 1L;
		
		
		
		//constructor			
		public rendering() {
			setFocusable(true); //so that can receive key-events
			requestFocus();
			addKeyListener(this);
			addMouseListener(this);
			addMouseMotionListener(this);
		}
		
		//overwrite paintComponent to do custom drawing
		//called back by repaint()
		public void paintComponent(Graphics g) {
			super.paintComponent(g);
			//paint background, may use an image for background
			//set background color
			
			Graphics2D g2 = (Graphics2D) g;
			g2.setRenderingHint(RenderingHints.KEY_ANTIALIASING,
            RenderingHints.VALUE_ANTIALIAS_ON);
			
			setBackground(Color.decode("0x3F919E"));
			
			//draw the game objects
			Draw(g);
		}
		
		
		
	  // function that performs the actual manipulation of the rubix cube
		
	   void rotary_action_perform(int action,int dangle) {
			
		   /* We don't need this one anymore (regularized before the input stage)
		    * 
		     if(dangle>3)        dangle= 3;
		     else if(dangle<-3)  dangle=-3;
		   */
		   
		   //some more work needs to be done here
		     
		     
			 int allow=1;
		       for(int i=0;i<9;i++) {
		       	 if(angle[i]!=0) {
		       		 if((i/3)!=(action/3)) allow=0; 
		       	 }
		        }
		   	 
		     
		     /*
		      *  the old version , where dangle input was variable and cube rest position was standardized
		      *  
		   	 if(allow>0 && (unallowed[action]==0)) {
		   		 
		     int sign  = (angle[action]%90)*((angle[action]+dangle)%90);
		     
		     int diff0 = ((  ((angle[action]+dangle)%90)  -  ((angle[action]%90)))   );
		     
		     
		     
		     
		   	 if(     (sign<0) ||
		   			 
		   			 (diff0!=dangle) ||
		   			 
		   			 ((Math.abs((angle[action]+dangle)%90)==0)&&(dangle!=0)) ) {                     
		   		 
		   		 int diff ;
		   		 
		   		      if(angle[action]>80)     diff=90-angle[action];
		   		 else if(angle[action]<-80)    diff=-90-angle[action]; 
		   		 else                  diff=          -angle[action];
		   		 
		   		 rotate_at_x(action,diff);
		   		 angle[action]=0; unallowed[action]=1; 
		   	 }
		   	  
		   	 else {rotate_at_x(action,dangle); angle[action]+=dangle;}
		   	 */
		       
		   	 if(allow>0 && (unallowed[action]==0)) {
		     rotate_at_x(action,dangle); 
		     angle[action]+=dangle;
		     
		     for(int i=0;i<3;i++) {
		    	 int index = ((action/3)*3)+i;
		    	 if(( angle[action]==angle[index]+90 ||
		    	      angle[action]==angle[index]-90 ||
		    	      angle[action]==angle[index]       ) && (action!=index)
		    			                                  && (Math.abs(action-index)==1) ) {
		    		 
		    		 
		    		 int lo_index = (((action/3)*3)*3)+(0+1+2)-action-index;;
		    		 
		    		 angle[lo_index]=(angle[lo_index]-angle[action])%90;
		    		 //System.out.println("rot all ref = "+action/3+" "+angle[action]);
		    		 rotate_all_reference(action/3,angle[index]);
		    		 angle[action]=0;
		    		 angle[index] =0;
		    		 unallowed[action]=1;
		    		 break;
		    	 }
		    			 
		   	 }
		   	 
		   	 set_distances();
			 reorder_objects();
			 repaint();
		   	 
		   	 }
		   	 
	    }
	    
	    //stops ongoing action 
		static void rotary_action_release(int action) {
		     
			if(unallowed[action]==1) unallowed[action]=0;
			   	 
	    }
			 
		//KeyEvent handlers
		@Override
		public void keyPressed(KeyEvent e) {
			/// place handler here
			 
			     if(e.getKeyCode()== KeyEvent.VK_LEFT ) { 
			    	 
			    	 rotate_all(2,-3);
			    	 set_distances();
			    	 reorder_objects();
			    	 repaint();
			    	 
			    	 
			     }
			     else if(e.getKeyCode()== KeyEvent.VK_RIGHT) {
				
			    	 rotate_all(2,3);
			    	 set_distances();
			    	 reorder_objects();
			    	 repaint();
			     }
			     else if(e.getKeyChar() <= '8' && e.getKeyChar() >= '0') {
			    	 
			    	 int action = e.getKeyChar() -'0';
			    	 rotary_action_perform(action,3);
			    	 
			     } 
			     else if(e.getKeyCode()== KeyEvent.VK_UP) {
						
			    	 rotate_all(1,3);
			    	 set_distances();
			    	 reorder_objects();
			    	 repaint();
			     }
			     else if(e.getKeyCode()== KeyEvent.VK_DOWN) {
						
			    	 rotate_all(1,-3);
			    	 set_distances();
			    	 reorder_objects();
			    	 repaint();
			     }
			     
			     /* I kept the camera Manipulation segment out of the program , although it works 
			      * it allows the camera to be rotated relative to the center of the cube
			      * and allows its position to be translated 
			      * if this is to be implemented -> the Gram schmidt process needs to be reimplemented to prevent 
			      * the accumulation of rounding errors 
			      */
			         
			 /*    else if(e.getKeyChar()=='d' || e.getKeyChar()=='D') {
			    	 
			    	 //derep_all();
			    	 c_p[0]+=6;
			    	 set_rep();
			    	 set_distances();
			    	 //rep_all();
			    	 for(object i : objects) reorder_content(i);
			    	 reorder_objects();
			  
			    	 repaint();
			    	 
			     }
			     else if(e.getKeyChar()=='q' || e.getKeyChar()=='Q') {
			    	 
			    	 //derep_all();
			    	 c_p[0]-=6;
			    	 set_rep();
			    	 //rep_all();
			    	 set_distances();
			    	 for(object i : objects) reorder_content(i);
			    	 reorder_objects();
			    	 
			    	 repaint();
			    	 
			     }
			     else if(e.getKeyChar()=='z' || e.getKeyChar()=='Z') {
			    	 
			    	 //derep_all();
			    	 c_p[1]-=6;
			    	 set_rep();
			    	 //rep_all();
			    	 set_distances();
			    	 for(object i : objects) reorder_content(i);
			    	 reorder_objects();
			    	 
			    	 repaint();
			    	 
			     }
			     else if(e.getKeyChar()=='s' || e.getKeyChar()=='S') {
			    	 
			    	 //derep_all();
			    	 c_p[1]+=6;
			    	 set_rep();
			    	 //rep_all();
			    	 set_distances();
			    	 for(object i : objects) reorder_content(i);
			    	 reorder_objects();
                     
			    	 repaint();
			    	 
			     }
			     if(e.getKeyChar()== 'v' ) { 
			    	 
			    	 //derep_all();
			    	 rotate_camera(1,3);
			    	 set_rep();
			    	 //rep_all();
			    	 set_distances();
			    	 for(object i : objects) reorder_content(i);
			    	 reorder_objects();
			    	 repaint();
			    	 
			    	 
			     }
			     else if(e.getKeyChar()== 'k') {
				      
                         System.out.println("printing lengths : ");
                         System.out.println("VZ = "+Math.sqrt(squared_length_3(cube_vz)));
                         System.out.println("VX = "+Math.sqrt(squared_length_3(cube_vx)));
                         System.out.println("VY = "+Math.sqrt(squared_length_3(cube_vy)));
			     }
			     else if(e.getKeyChar()== 'x') {
				      
			    	 //derep_all();
			    	 rotate_camera(1,-3);
			    	 set_rep();
			    	 //rep_all();
			    	 set_distances();
			    	 
			    	 for(object i : objects) reorder_content(i);
			    	 reorder_objects();
			    	 
			    	 repaint();
			     }
			     else if(e.getKeyChar()== 'f') {
			    	 //derep_all();
			    	 rotate_camera(0,3);
			    	 set_rep();
			    	 //rep_all();
			    	 set_distances();
			    	 
			    	 for(object i : objects) reorder_content(i);
			    	 reorder_objects();
			    	 
			    	 repaint();
			     }
			     else if(e.getKeyChar()== 'c') {
			    	 //derep_all();
			    	 rotate_camera(0,-3);
			    	 set_rep();
			    	 //rep_all();
			    	 set_distances();
			    	 
			    	 for(object i : objects) reorder_content(i);
			    	 reorder_objects();
			    	 
			    	 repaint();
			     }*/
		}

		@Override
		public void keyReleased(KeyEvent e) {
	    	if(e.getKeyChar() <= '8' && e.getKeyChar() >= '0') {
		    	 
                   int action = e.getKeyChar()-'0';
                   rotary_action_release(action);
		    	 
		     } 
			
		}

		@Override
		public void keyTyped(KeyEvent e) {
			// TODO Auto-generated method stub
			
		}
		
		public void mousePressed(MouseEvent e) {   
			int obj = (codex[e.getY()][e.getX()]%100)-1;
	           if(obj>-1) {
	           primer=obj;
	           }
		}  
		public void mouseMoved(MouseEvent e) {}  
		
		// Mouse events handlers , to allow manipulation of the cube through mouse movements 
		@Override
		public void mouseDragged(MouseEvent e) {
			if(mx==0) mx=e.getX();  
			if(my==0) my=e.getY(); 
			
			int dx=e.getX()-mx;
			int dy=e.getY()-my;
			
			double[] disp_vector = new double[4];
			
			disp_vector[0]=dx;
			disp_vector[1]=dy;
			disp_vector[2]=0;
			disp_vector[3]=1;
		
			disp_vector = scv(disp_vector, (1/Math.sqrt(squared_length_3(disp_vector))));
			disp_vector[3]=1;
			
			//System.out.println("pressed");
			
			 if(primer!=999) {
					  if(activation!=0) {
						  int d=0;
						       if(vector==1) d=dir_sign*dx;
						  else if(vector==2) d=dir_sign*dy;
						  
						  
						  if(Math.abs(d)>=3) { 
						  int d_sign; 
						  if(d<0) d_sign=-1; else d_sign=1;
						  d=d_sign*3;
						  rotary_action_perform(action,d*activation);
						  mx=e.getX();
						  my=e.getY();
						  }
					  } else if(((dx*dx)+(dy*dy)>100)){
						   
						     int primer_loc = 0;
						     
						     for(int i=0;i<objects.size();i++) {
						    	 if(objects.get(i).attribute==primer) {
						    		 primer_loc=i;
						    		 break;
						    	 }
						     }
						     
						     double[][]   rot_axle        = new double[3][4];
							 double[][][] rotation_matrix = new double[3][2][16];
							 double[]          inv_matrix = new double[16];
							 inv_matrix                  = calculate_inv_matrix     (cube_p,cube_vx,cube_vy,cube_vz);
							 
							 double[][]      rot_orig = new double[3][4];
							 double[][]      test_vs  = new double[6][4];
							 
							 double[] ocenter = new double[4];
							 ocenter = mv(inv_matrix,objects.get(primer_loc).center);
							 
							 rot_axle[0] = cube_vz;
							 rot_axle[1] = cube_vx;
							 rot_axle[2] = cube_vy;
							 
							 int[] pos_ = new int[3];
							 
							 
							 rot_orig[0] = av(cube_p,1,rot_axle[0],ocenter[2]); pos_[0]=(int)Math.round((ocenter[2]/(cube_l/3))+1);
						     rot_orig[1] = av(cube_p,1,rot_axle[1],ocenter[0]); pos_[1]=(int)Math.round((ocenter[0]/(cube_l/3))+1);
						     rot_orig[2] = av(cube_p,1,rot_axle[2],ocenter[1]); pos_[2]=(int)Math.round((ocenter[1]/(cube_l/3))+1);
							 
						
							 
							 /////////// les axes  0-Z , 1-X , 2-Y
							 rotation_matrix[0][0] = calculate_rotation_matrix(rot_orig[0],cube_vx,cube_vy,cube_vz,0,10);
							 rotation_matrix[0][1] = calculate_rotation_matrix(rot_orig[0],cube_vx,cube_vy,cube_vz,0,-10);
							 
							 rotation_matrix[1][0] = calculate_rotation_matrix(rot_orig[1],cube_vx,cube_vy,cube_vz,1,10);
							 rotation_matrix[1][1] = calculate_rotation_matrix(rot_orig[1],cube_vx,cube_vy,cube_vz,1,-10);
							 
							 rotation_matrix[2][0] = calculate_rotation_matrix(rot_orig[2],cube_vx,cube_vy,cube_vz,2,10);
							 rotation_matrix[2][1] = calculate_rotation_matrix(rot_orig[2],cube_vx,cube_vy,cube_vz,2,-10);
							 
							 int   i_exception     = 0;
							 int   i_target        = 0;
							 double dt=0;
							 
							 for(int i=0;i<3;i++) {
								 double t  = Math.abs(dot_product_h(c_z,rot_axle[i]));
								 if(t>dt) {i_exception=i; dt=t;}
							 }
							 
							 
							 dt=0;
							 int first_t=0;
							 for(int i=0;i<3;i++) {
								 if(i!=i_exception) {
								 double t  = Math.abs(dot_product_h(disp_vector,rot_axle[i]));
		                         if(first_t==0) {dt=t; first_t=1;}
								 if(t<=dt) {i_target=i; dt=t;}
								 }
							 }
							 
							 //Systeout.println("rot orig : "+rot_orig[i_target][0]+" "+rot_orig[i_target][1]+" "+rot_orig[i_target][2]);
							 
							 double[] ocenter_rep = new double[4];
							 ocenter_rep = mv(rep,objects.get(primer_loc).center);
							 ocenter_rep[0]/=ocenter_rep[3];
							 ocenter_rep[1]/=ocenter_rep[3];
							 
							 //System.out.println("from ocrep : "+ocenter_rep[0]+" "+ocenter_rep[1]+" "+ocenter_rep[2]+"  ");
							 
							 double dot_p=0;
							 int   last_i=0;
							 double[] z_ = new double[60];
							 
							 //System.out.println("itarget is "+i_target);
							 
							 for(int i=0;i<2;i++) {
								 double temp_dp;
								 
								 double[] temp_center = new double[4];
								 
								         temp_center[0] = objects.get(primer_loc).center[0];
								         temp_center[1] = objects.get(primer_loc).center[1];
								         temp_center[2] = objects.get(primer_loc).center[2];
								         temp_center[3] = objects.get(primer_loc).center[3];
								         
								         temp_center[2]-=600;
								         
								 test_vs[(i_target*2)+i]=mv(rotation_matrix[i_target][i],temp_center); 
								 test_vs[(i_target*2)+i]=mv(rep,test_vs[(i_target*2)+i]);
								 
								 test_vs[(i_target*2)+i][0]=test_vs[(i_target*2)+i][0]/test_vs[(i_target*2)+i][3];
								 test_vs[(i_target*2)+i][1]=test_vs[(i_target*2)+i][1]/test_vs[(i_target*2)+i][3];
								 test_vs[(i_target*2)+i][2]=0; //for it to be correct
								 z_[(i_target*2)+i] = test_vs[(i_target*2)+i][3]; 
								 test_vs[(i_target*2)+i][3]=1;
								 
								 //System.out.println("to testvs : "+test_vs[(i_target*2)+i][0]+" "+test_vs[(i_target*2)+i][1]+" "+test_vs[(i_target*2)+i][2]+"  ");
								 
								 test_vs[(i_target*2)+i][0]-=ocenter_rep[0];
								 test_vs[(i_target*2)+i][1]-=ocenter_rep[1];
								 //z_[(i_target*2)+i]        -=ocenter_rep[3];
								 
								 //test_vs[(i_target*2)+i]   = scv(test_vs[(i_target*2)+i],1/Math.sqrt(squared_length_3(test_vs[(i_target*2)+i])));
								 test_vs[(i_target*2)+i][3]=1;
								 
								 temp_dp = dot_product_h(test_vs[(i_target*2)+i],disp_vector);
								 
								 //System.out.println(i+" temp_dp = "+temp_dp);
								 
								 
							     if(temp_dp>=dot_p) { 
							    	 double ratio = temp_dp/dot_p;
							    	 /*if(!((ratio>=0)&&(ratio>=0.5&&ratio<=1.5))) {*/ dot_p=temp_dp; last_i=(i_target*2)+i; //+3.}
							     }	 
							 }
							 
							 //System.out.println("chosen : "+(last_i%2));
							 
							 
							 action=((last_i/2)*3)+pos_[last_i/2];
							 
							 if(last_i%2==0) activation=1; else activation=-1;
							 //System.out.println("activation = "+activation);
							 if(Math.abs(dx)>=Math.abs(dy)) {vector=1; if(dx<0) dir_sign = -1; else dir_sign = 1; }
							 else {vector=2; if(dy<0) dir_sign = -1; else dir_sign = 1; }
							 
						 
				      }    
				 
			 }
			 
	    }

		@Override
	    public void mouseReleased(MouseEvent e) {
			
			//System.out.println("released");
			for(int i=0;i<9;i++) rotary_action_release(i);
			primer=999;
			activation=0;
			vector=0;
			action=0;
			dir_sign=0;
			mx=0; my=0;
			

	    }

		@Override
	    public void mouseEntered(MouseEvent e) {

	    }

		@Override
	    public void mouseExited(MouseEvent e) {

	    }

		@Override
	    public void mouseClicked(MouseEvent e) { 
			/*
	           int obj = (codex[e.getY()][e.getX()]%100)-1;
	           if(obj>-1) {
	           primer=obj;
	           for(int i=0;i<objects.size();i++) {
	        	   if(objects.get(i).attribute == (obj)) { 
	        		        if(e.getButton()==e.BUTTON3) objects.remove(i);
	        		        repaint(); break;
	        	   }
	              }
	           } */
	           
	           
	    }
		
		
		
	}
	
	

	//makes the squares that constitue the mini-cubes
	//position of the center point of the square element
	static void make_square(ArrayList<polygone> arr,int i, double[] x,double l,Color col,int attr,int ipos) {
		
    	ArrayList<polygone> p = new ArrayList<polygone>();
    	polygone p1 = new polygone();
    	polygone p2 = new polygone();
    	p.add(p1); p.add(p2);
    	
        double[][]  temp_va = new double[4][4];
    	
    	for(int j=0;j<4;j++) {for(int k=0;k<4;k++)  {
    		
    		      temp_va[j][k]=(cube[(i*4)+j][k]*(l/2))+x[k]+(cube_correction[i][k]*(l/2));
    		      
    		                                         }
    	                      
    	                      }
    	
    	for(int k=0;k<6;k++) {   // t ---> 0-1-2-2-3-0
    		
    		      int t = ((k%3)+((k/3)*2))%4;
    		      
    		      temp_va[t][3]=1;
    		      p.get(k/3).vector[k%3] = temp_va[t];
    		      
    		      if((k%3)==2) {
    		    	  p.get(k/3).color     = col;
    		    	  p.get(k/3).face      = i;
    			      if(attr>0)  p.get(k/3).attribute=attr;
    		    	  if(ipos==0) arr.add(0,p.get(k/3)); else arr.add(p.get(k/3));
    		      }
    	}
    	
	}
	
	/*
	static polygone make_square(int i, double[] x,double l,Color col) {
		
    	polygone p = new polygone();
    	double[] cp= {0,0,0,0};
    	
    	double   fd=0;
    	double   cd=0;
    	
    	for(int j=0;j<4;j++) {for(int k=0;k<4;k++)  {
    		
    		      p.vector[j][k]=(cube[(i*4)+j][k]*(l/2))+x[k]+(cube_correction[i][k]*(l/2));
    		      
    		                                         }
    	                      
    	                      cp = av(cp,p.vector[j]);} 
    	                      cp = scv(cp,0.25);
    	p.center    = cp;
    	p.distance  = squared_distance_h(cp,c_p);
    	p.color     = col;
    	
    	return p;
	} */
	
	//constructs a mini-cube
	static object make_cube(double[] x,double l,Color col,int attr) {
		
	    object cube = new object();
	    for(int i=0;i<6;i++) {
	    	make_square(cube.content,i,sv(x,cube_correction[i],l/2),l,col,attr,1); //adds two at a toùe   
	    }  
	    return cube;

	}
	
	// main function
	public static void main(String[] args) {
		//use the event dispatch thread to build the UI for thread-safety
		
           
		    //define cube colors as such F-R-B-L-U-D , Rubix cube colors : Green - Red - Yellow - Orange - White - Blue
		    ArrayList<Color> cube_colors = new ArrayList<Color>();
		    cube_colors.add(Color.green);
		    cube_colors.add(Color.red);
		    cube_colors.add(Color.yellow);
		    cube_colors.add(orange);
		    cube_colors.add(Color.white);
		    cube_colors.add(Color.blue);
		    //for(int i=0;i<6;i++) cube_colors.add(Color.white);
		    
		    
		    //construct the Rubix Cube 
		    //constructing the black mini-cubes themselves
            for(int i=0;i<3;i++) {
            	for(int j=0;j<9;j++) {
            		   double bv[] = {(-cube_l/3)+((j%3)*(cube_l/3)),
            				         (-cube_l/3)+((j/3)*(cube_l/3)),
            				         (-cube_l/3)+( i   *(cube_l/3)),
            				           0};
            		   
                       object cube = new object();
                              cube = make_cube(av(bv,cube_p),cube_l/3,Color.black,'b');
                              cube.attribute = (i*9)+j;
                              objects.add(cube);
                               
            	}       
            }
            set_distances();
            
            //adding the colors 
            for(int i=0;i<6;i++) {
            	
            	for(int j=0;j<9;j++) {
            		
            		int  coeff =
            		((int)Math.abs(cube_correction[i][0])*9)+
            		((int)Math.abs(cube_correction[i][1])*1)+
            		((int)Math.abs(cube_correction[i][2])*1);
            		
            		int scoeff =
            		((int)Math.abs(cube_correction[i][0])*3)+
                    ((int)Math.abs(cube_correction[i][1])*9)+
                    ((int)Math.abs(cube_correction[i][2])*3);
            		
            		int start  = 0;
            		     if(-cube_correction[i][0]== 1) start= 2;
            		else if(-cube_correction[i][0]==-1) start= 0;
            		else if(-cube_correction[i][1]== 1) start= 6;
            		else if(-cube_correction[i][1]==-1) start= 0;
            		else if(-cube_correction[i][2]== 1) start=18;
            		else if(-cube_correction[i][2]==-1) start= 0;   
            		
            		int index = start + ((j%3)*coeff) + ((j/3)*scoeff);
            		  		
            		             make_square(objects.get(index).content,
            		            		     i, 
            				                 sv(objects.get(index).center,cube_correction[i],cube_l/6),
            				                 (cube_l/3)-20,
            				                 cube_colors.get(i),0,0);
            		     
            		
            		
            	}
            }
		    
		    set_distances();
		    set_rep();
		
		SwingUtilities.invokeLater(new Runnable() {
			public void run() {
				JFrame frame = new JFrame(TITLE);
			    Dimension d = new Dimension();
			    d.height = (int)Math.round(H);
			    d.width  = (int)Math.round(L);
				frame.setPreferredSize(d);
				frame.setResizable(false);
				
				// main JPanel as content pane
                frame.setContentPane(new Rubix());				
				frame.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
				frame.pack();
				//center the app window
				frame.setLocationRelativeTo(null);
				//show the frame
				frame.setVisible(true);
			
			}
		});
	}
}              /// Thank you for reading 