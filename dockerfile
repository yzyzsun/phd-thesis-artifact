FROM coqorg/coq:8.13.2 as  build
LABEL maintainer="Baber Rehamn"

RUN ["/bin/bash", "--login", "-c", "set -x \
  && opam repository add --all-switches --set-default coq-released https://coq.inria.fr/opam/released"]

# install coq TLC library

RUN ["/bin/bash", "--login", "-c", "set -x \
  && opam install -y coq-tlc.20210316"]
  
# install metalib/metatheory coq library

RUN ["/bin/bash", "--login", "-c", "set -x \
  && git clone https://github.com/plclub/metalib.git --branch coq8.10 --single-branch"]

WORKDIR /home/coq/metalib/Metalib

RUN ["/bin/bash", "--login", "-c", "set -x \
  && make"]
  
RUN ["/bin/bash", "--login", "-c", "set -x \
  && make install"]
 
# copy coq code from local to docker image  
  
WORKDIR /home/coq

RUN ["/bin/bash", "--login", "-c", "set -x \
  && git clone https://github.com/baberrehman/phd-thesis-artifact.git"]

#COPY --chown=coq code /home/coq/code

# cleanup - delete unnecessary metalib files
  
RUN ["/bin/bash", "--login", "-c", "set -x \
  && rm -r metalib"]
  
RUN ["/bin/bash", "--login", "-c", "set -x \
  && sudo apt update -y"]
  
RUN ["/bin/bash", "--login", "-c", "set -x \
  && sudo apt install vim -y"]

#WORKDIR /home/coq/coq-duotyping/coq/DuoTyping

#RUN ["/bin/bash", "--login", "-c", "set -x \
#  && make"]
