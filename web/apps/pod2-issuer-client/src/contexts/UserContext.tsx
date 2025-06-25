import { createContext, useContext, useState } from "react";
import type { ReactNode } from "react";

interface UserContextType {
  username: string;
  publicKey: string;
  password: string;
  isLoggedIn: boolean;
  login: (username: string, password: string) => Promise<void>;
  logout: () => void;
}

const UserContext = createContext<UserContextType | undefined>(undefined);

export function UserProvider({ children }: { children: ReactNode }) {
  const [username, setUsername] = useState(
    localStorage.getItem("username") ?? ""
  );
  const [publicKey, setPublicKey] = useState(
    localStorage.getItem("publicKey") ?? ""
  );
  const [password, setPassword] = useState(
    localStorage.getItem("password") ?? ""
  );
  const [isLoggedIn, setIsLoggedIn] = useState(
    username !== "" && publicKey !== "" && password !== ""
  );

  const login = async (username: string, password: string) => {
    const response = await fetch(`${import.meta.env.VITE_API_URL}/api/hash`, {
      method: "POST",
      body: JSON.stringify(password),
    });

    const publicKey = await response.json();

    localStorage.setItem("username", username);
    localStorage.setItem("publicKey", publicKey);
    localStorage.setItem("password", password);
    setUsername(username);
    setPublicKey(publicKey);
    setPassword(password);
    setIsLoggedIn(true);
  };

  const logout = () => {
    localStorage.removeItem("username");
    localStorage.removeItem("publicKey");
    localStorage.removeItem("password");
    setUsername("");
    setPublicKey("");
    setPassword("");
    setIsLoggedIn(false);
  };

  return (
    <UserContext.Provider
      value={{
        username,
        publicKey,
        password,
        isLoggedIn,
        login,
        logout,
      }}
    >
      {children}
    </UserContext.Provider>
  );
}

export function useUser() {
  const context = useContext(UserContext);
  if (context === undefined) {
    throw new Error("useUser must be used within a UserProvider");
  }
  return context;
}
