FROM node:20

ARG TZ
ENV TZ="$TZ"

ARG CLAUDE_CODE_VERSION=latest

# Install basic development tools and iptables/ipset
RUN apt-get update && apt-get install -y --no-install-recommends \
  less \
  git \
  procps \
  sudo \
  fzf \
  zsh \
  man-db \
  unzip \
  gnupg2 \
  gh \
  iptables \
  ipset \
  iproute2 \
  dnsutils \
  aggregate \
  jq \
  nano \
  vim \
  && apt-get clean && rm -rf /var/lib/apt/lists/*

# Ensure default node user has access to /usr/local/share
RUN mkdir -p /usr/local/share/npm-global && \
  chown -R node:node /usr/local/share

ARG USERNAME=node

# Persist bash history.
RUN SNIPPET="export PROMPT_COMMAND='history -a' && export HISTFILE=/commandhistory/.bash_history" \
  && mkdir /commandhistory \
  && touch /commandhistory/.bash_history \
  && chown -R $USERNAME /commandhistory

# Set `DEVCONTAINER` environment variable to help with orientation
ENV DEVCONTAINER=true

# Create workspace and config directories and set permissions
RUN mkdir -p /workspace /home/node/.claude && \
  chown -R node:node /workspace /home/node/.claude

WORKDIR /workspace

ARG GIT_DELTA_VERSION=0.18.2
RUN ARCH=$(dpkg --print-architecture) && \
  wget "https://github.com/dandavison/delta/releases/download/${GIT_DELTA_VERSION}/git-delta_${GIT_DELTA_VERSION}_${ARCH}.deb" && \
  sudo dpkg -i "git-delta_${GIT_DELTA_VERSION}_${ARCH}.deb" && \
  rm "git-delta_${GIT_DELTA_VERSION}_${ARCH}.deb"

# Install global packages
ENV NPM_CONFIG_PREFIX=/usr/local/share/npm-global
ENV PATH=$PATH:/usr/local/share/npm-global/bin

# Set the default shell to zsh rather than sh
ENV SHELL=/bin/zsh

# Set the default editor and visual
ENV EDITOR=nano
ENV VISUAL=nano

# Default powerline10k theme
ARG ZSH_IN_DOCKER_VERSION=1.2.0
RUN sh -c "$(wget -O- https://github.com/deluan/zsh-in-docker/releases/download/v${ZSH_IN_DOCKER_VERSION}/zsh-in-docker.sh)" -- \
  -p git \
  -p fzf \
  -a "source /usr/share/doc/fzf/examples/key-bindings.zsh" \
  -a "source /usr/share/doc/fzf/examples/completion.zsh" \
  -a "export PROMPT_COMMAND='history -a' && export HISTFILE=/commandhistory/.bash_history" \
  -x

# Install Claude
RUN npm install -g @anthropic-ai/claude-code@${CLAUDE_CODE_VERSION}


# Copy and set up firewall script
COPY init-firewall.sh /usr/local/bin/
RUN chmod +x /usr/local/bin/init-firewall.sh && \
  echo "node ALL=(root) NOPASSWD: /usr/local/bin/init-firewall.sh" > /etc/sudoers.d/node-firewall && \
  chmod 0440 /etc/sudoers.d/node-firewall

# ---------------------------------------------------------------------------
# Research toolchain for docs/plan.md section 6.2 (exact synthesis). Everything
# below runs at image build time, where the runtime firewall does not apply.
# Pins are recorded in docs/plan.md section 8; bump them there and here together.
# Deferred on purpose (see plan section 8): elan/Lean, D4, c2d, CUDD/DecisionDiagrams.
# ---------------------------------------------------------------------------

# Build tools for the SAT solvers and Python packaging. node:20 (Debian bookworm)
# already ships the .NET runtime dependencies (libicu72, libssl3, libgssapi-krb5-2,
# libstdc++6, zlib1g, ca-certificates), so they are not listed here.
RUN apt-get update && apt-get install -y --no-install-recommends \
  build-essential \
  python3 \
  python3-pip \
  python3-venv \
  && apt-get clean && rm -rf /var/lib/apt/lists/*

# CaDiCaL, Kissat and drat-trim from pinned GitHub release tags. Each has a plain
# configure/make build with no dependencies beyond a C/C++ compiler.
ARG CADICAL_VERSION=3.0.1
ARG KISSAT_VERSION=4.0.4
ARG DRAT_TRIM_VERSION=05.22.2023
RUN set -eux; \
  git clone --depth 1 --branch "rel-${CADICAL_VERSION}" https://github.com/arminbiere/cadical.git /tmp/cadical; \
  cd /tmp/cadical && ./configure && make -j"$(nproc)"; \
  install -m 0755 /tmp/cadical/build/cadical /usr/local/bin/cadical; \
  cd / && rm -rf /tmp/cadical; \
  cadical --version
RUN set -eux; \
  git clone --depth 1 --branch "rel-${KISSAT_VERSION}" https://github.com/arminbiere/kissat.git /tmp/kissat; \
  cd /tmp/kissat && ./configure && make -j"$(nproc)"; \
  install -m 0755 /tmp/kissat/build/kissat /usr/local/bin/kissat; \
  cd / && rm -rf /tmp/kissat; \
  kissat --version
RUN set -eux; \
  git clone --depth 1 --branch "v${DRAT_TRIM_VERSION}" https://github.com/marijnheule/drat-trim.git /tmp/drat-trim; \
  cd /tmp/drat-trim && make drat-trim; \
  install -m 0755 /tmp/drat-trim/drat-trim /usr/local/bin/drat-trim; \
  cd / && rm -rf /tmp/drat-trim; \
  command -v drat-trim

# .NET 10 SDK (LTS, supported until 2028-11-14). .NET 8 reaches end of support on
# 2026-11-10. --version pins the exact SDK build; --channel is kept for clarity and
# is what the script falls back to if --version is removed.
ARG DOTNET_CHANNEL=10.0
ARG DOTNET_SDK_VERSION=10.0.403
ENV DOTNET_ROOT=/usr/share/dotnet \
  DOTNET_CLI_TELEMETRY_OPTOUT=1 \
  DOTNET_NOLOGO=1 \
  DOTNET_CLI_WORKLOAD_UPDATE_NOTIFY_DISABLE=1 \
  DOTNET_GENERATE_ASPNET_CERTIFICATE=false
RUN set -eux; \
  curl -fsSL https://dot.net/v1/dotnet-install.sh -o /tmp/dotnet-install.sh; \
  bash /tmp/dotnet-install.sh \
    --channel "${DOTNET_CHANNEL}" \
    --version "${DOTNET_SDK_VERSION}" \
    --install-dir "${DOTNET_ROOT}" \
    --no-path; \
  rm /tmp/dotnet-install.sh; \
  ln -s "${DOTNET_ROOT}/dotnet" /usr/local/bin/dotnet; \
  dotnet --version
ENV PATH=$PATH:/usr/share/dotnet:/home/node/.dotnet/tools

# Python venv for throwaway checks (scripts/*.py). Owned by node so further
# packages (matplotlib, pandas, deferred) can be added at runtime through the
# firewall. networkx 3.7 requires Python >= 3.12; bookworm ships 3.11, so 3.6.1.
ARG PYTHON_SAT_VERSION=1.9.dev21
ARG NETWORKX_VERSION=3.6.1
ENV VIRTUAL_ENV=/opt/venv
RUN set -eux; \
  python3 -m venv "${VIRTUAL_ENV}"; \
  "${VIRTUAL_ENV}/bin/pip" install --no-cache-dir \
    "python-sat==${PYTHON_SAT_VERSION}" \
    "networkx==${NETWORKX_VERSION}"; \
  chown -R node:node "${VIRTUAL_ENV}"; \
  "${VIRTUAL_ENV}/bin/python" -c "import pysat, networkx"
ENV PATH=/opt/venv/bin:$PATH

# Set up non-root user
USER node
