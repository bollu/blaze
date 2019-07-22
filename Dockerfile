# Dockerfile
# docker build -t user .
FROM haskell:8.2.2

# Install dependecies needed
RUN apt-get update && apt-get install -y \
    curl \
    libmagic-dev \
    libzmq3-dev \
    libpango1.0-dev \
    python3-pip \
    r-base \
    z3

# Install R package ggplot2
RUN R -e "install.packages(c('ggplot2'), repos='http://cran.rstudio.com/')"

# Install NodeJS
RUN curl -sSL https://deb.nodesource.com/setup_8.x | bash && \
    apt-get install -y nodejs

# Install Jupyter notebook
RUN pip3 install jupyterlab==0.33.0 && \
    jupyter labextension install ihaskell_jupyterlab

# Setup the haskell environment
ENV DG_USER user
ENV DG_UID 1000
ENV DG_HOME /home/${DG_USER}
RUN adduser --disabled-password --gecos "Default user" --uid ${DG_UID} ${DG_USER}

# Set up a working directory for IHaskell
WORKDIR ${DG_HOME}
COPY . .

# Install dependencies for IHaskell
RUN chown -R ${DG_UID} ${DG_HOME}
USER ${DG_UID}

RUN stack build && \
    stack install && \
    stack exec -- ihaskell install --stack

EXPOSE 8888

# Run the notebook
CMD ["stack", "exec", "jupyter", "notebook"]
# CMD ["stack", "exec", "--", "jupyter", "lab", "--ip", "0.0.0.0"]

