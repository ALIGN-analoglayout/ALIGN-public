import numpy as np
import matplotlib.pyplot as plt
import rc_data
import math
import tensorflow as tf
from tensorflow.python.framework.graph_util import convert_variables_to_constants

def main():
    dataset = rc_data.rc_data('../../Data/rc_amplifier_tsmc180.npz')
    label_name = dataset.label_name
    train_x = dataset.train_x
    train_y = dataset.train_y_norm

    fp = open('result.log','w+')
    label_set =range(5) 
    #for index in range(label_name.size):
    for index in label_set:
        model_name = label_name[index]
        train_yi = train_y[:,index].squeeze()

        with tf.variable_scope(model_name.replace(" ", "_")):
            sess = tf.Session()
            inputs = tf.placeholder("float", shape=(None, train_x.shape[1]))
            labels = tf.placeholder("float", shape=(None))
            learning_rate = 0.001
            epoches = 10
            hidden1 = tf.layers.dense(inputs, 30, activation = tf.nn.relu, name = "hidden1")
            hidden2 = tf.layers.dense(hidden1, 7, activation = tf.nn.relu, name = "hidden2")
            outputs = tf.layers.dense(hidden2, 1, activation = tf.nn.relu, name = "outputs")
            losses = tf.reduce_mean(tf.losses.mean_squared_error(outputs, labels))
            train_op = tf.train.GradientDescentOptimizer(learning_rate = learning_rate).minimize(losses)
            #saver = tf.train.Saver(var_list=tf.global_variables(), max_to_keep=0)
            sess.run(tf.global_variables_initializer())
            for epoch in range(epoches):
                feed_dict = {inputs: train_x, labels: train_yi}
                loss, _ = sess.run([losses, train_op], feed_dict=feed_dict)
                print('Epoch {:d}/{:d} Loss {:.6f}'.format(epoch, epoches, loss), end='\r', flush=True)
                #saver.save(sess, "models/" + model_name + ".ckpt")
            print(outputs)
            graph = convert_variables_to_constants(sess, sess.graph_def, [model_name.replace(" ", "_") + "/outputs/Relu"])
            tf.train.write_graph(graph,'models',model_name.replace(" ", "_")+'.pb',as_text=False)
            sess.close()
        

        '''test_x = dataset.test_x
        test_y = dataset.test_y
        test_yi = test_y[:,index]
        pred_yi = model.predict(test_x)
        pred_yi = dataset.denorm(pred_yi, index)
        fp.write('Training result for '+model_name+'\n')
        fp.write('sqrt mse  : '+str(math.sqrt(mse(pred_yi, test_yi)))+'\n')
        fp.write('label mean: '+str(np.mean(test_yi))+'\n'+'\n')

        plt.figure()
        plt.scatter(test_yi, pred_yi)
        plt.xlabel('test')
        plt.ylabel('pred')
        plt.plot([np.amin(test_yi), np.amax(test_yi)],[np.amin(test_yi), np.amax(test_yi)], color='C1')
        plt.savefig('./figs/'+model_name+'_pred.eps')
        '''

if __name__ == '__main__':
    main()
